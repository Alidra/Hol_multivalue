Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_MULT_MOD_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import DIV_DIV_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import MOD_ZERO_spec.
Require Import MULT_AC_spec.
Require Import MULT_CLAUSES_spec.
Require Import MULT_SYM_spec.
Require Import REFL_CLAUSE_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm161359_spec.
Require Import thm161362_spec.
Require Import thm161369_spec.
Require Import thm161372_spec.
Require Import thm16474_spec.
Require Import thm16597_spec.
Require Import thm16684_spec.
Require Import thm16799_spec.
Require Import thm16917_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21816_spec.
Require Import thm21930_spec.
Require Import thm22025_spec.
Require Import thm22288_spec.
Require Import thm22403_spec.
Require Import thm22518_spec.
Require Import thm32_spec.
Require Import thm69_spec.
Lemma lem227407 : term0.
Proof. exact (EQ_MP (@lem161362) (@lem161359)). Qed.
Lemma lem227408 (m : nat) : term1 m.
Proof. exact (@lem227407 m). Qed.
Lemma lem227409 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem227410 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem227409 m) (@lem227408 m)). Qed.
Lemma lem227411 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem227410 m n). Qed.
Lemma lem227412 (n : nat) (m : nat) : (term3 m n) = ((term4 m n) = m).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem227414 : term5.
Proof. exact (EQ_MP (@lem161372) (@lem161369)). Qed.
Lemma lem227415 (m : nat) : term6 m.
Proof. exact (@lem227414 m). Qed.
Lemma lem227416 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem227417 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem227416 m) (@lem227415 m)). Qed.
Lemma lem227418 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem227417 m n). Qed.
Lemma lem227419 (n : nat) (m : nat) : (term8 m n) = ((term9 m n) = m).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem227424 (m : nat) (n : nat) (p : nat) (h1 : (term10 m n p) = (term11 m n p)) : (term10 m n p) = (term11 m n p).
Proof. exact (h1). Qed.
Lemma lem227425 (m : nat) (n : nat) (p : nat) (h1 : (term10 m n p) = (term11 m n p)) : (term11 m n p) = (term10 m n p).
Proof. exact (SYM (@lem227424 m n p h1)). Qed.
Lemma lem227426 (m : nat) (n : nat) (p : nat) (h1 : (term11 m n p) = (term10 m n p)) : (term11 m n p) = (term10 m n p).
Proof. exact (h1). Qed.
Lemma lem227427 (m : nat) (n : nat) (p : nat) (h1 : (term11 m n p) = (term10 m n p)) : (term10 m n p) = (term11 m n p).
Proof. exact (SYM (@lem227426 m n p h1)). Qed.
Lemma lem227428 (m : nat) (n : nat) (p : nat) : ((term10 m n p) = (term11 m n p)) = ((term11 m n p) = (term10 m n p)).
Proof. exact (prop_ext (fun h1 : (term10 m n p) = (term11 m n p) => @lem227425 m n p h1) (fun h1 : (term11 m n p) = (term10 m n p) => @lem227427 m n p h1)). Qed.
Lemma lem227429 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (fun_ext (fun p : nat => @lem227428 m n p)). Qed.
Lemma lem227430 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227431 (m : nat) (n : nat) : (term14 m n) = (term15 m n).
Proof. exact (MK_COMB (@lem227430) (@lem227429 m n)). Qed.
Lemma lem227432 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem227431 m n)). Qed.
Lemma lem227433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227434 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem227433) (@lem227432 m)). Qed.
Lemma lem227435 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem227434 m)). Qed.
Lemma lem227436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227437 : term22 = term23.
Proof. exact (MK_COMB (@lem227436) (@lem227435)). Qed.
Lemma lem227438 : term23.
Proof. exact (EQ_MP (@lem227437) (@lem220350)). Qed.
Lemma lem227442 (n : nat) (m : nat) (p : nat) (h1 : (term24 m n p) = (term25 n m p)) : (term24 m n p) = (term25 n m p).
Proof. exact (h1). Qed.
Lemma lem227443 (n : nat) (m : nat) (p : nat) (h1 : (term24 m n p) = (term25 n m p)) : (term25 n m p) = (term24 m n p).
Proof. exact (SYM (@lem227442 n m p h1)). Qed.
Lemma lem227444 (m : nat) (n : nat) (p : nat) (h1 : (term25 n m p) = (term24 m n p)) : (term25 n m p) = (term24 m n p).
Proof. exact (h1). Qed.
Lemma lem227445 (m : nat) (n : nat) (p : nat) (h1 : (term25 n m p) = (term24 m n p)) : (term24 m n p) = (term25 n m p).
Proof. exact (SYM (@lem227444 m n p h1)). Qed.
Lemma lem227446 (m : nat) (n : nat) (p : nat) : ((term24 m n p) = (term25 n m p)) = ((term25 n m p) = (term24 m n p)).
Proof. exact (prop_ext (fun h1 : (term24 m n p) = (term25 n m p) => @lem227443 n m p h1) (fun h1 : (term25 n m p) = (term24 m n p) => @lem227445 m n p h1)). Qed.
Lemma lem227447 (m : nat) (n : nat) : (term26 n m) = (term27 m n).
Proof. exact (fun_ext (fun p : nat => @lem227446 m n p)). Qed.
Lemma lem227448 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227449 (m : nat) (n : nat) : (term28 n m) = (term29 m n).
Proof. exact (MK_COMB (@lem227448) (@lem227447 m n)). Qed.
Lemma lem227450 (m : nat) : (term30 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem227449 m n)). Qed.
Lemma lem227451 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227452 (m : nat) : (term32 m) = (term33 m).
Proof. exact (MK_COMB (@lem227451) (@lem227450 m)). Qed.
Lemma lem227453 : term34 = term35.
Proof. exact (fun_ext (fun m : nat => @lem227452 m)). Qed.
Lemma lem227454 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227455 : term36 = term37.
Proof. exact (MK_COMB (@lem227454) (@lem227453)). Qed.
Lemma lem227456 : term37.
Proof. exact (EQ_MP (@lem227455) (@lem82055)). Qed.
Lemma lem227457 (m : nat) : term38 m.
Proof. exact (@lem227438 m). Qed.
Lemma lem227458 (m : nat) : (term38 m) = (term19 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem227459 (m : nat) : term19 m.
Proof. exact (EQ_MP (@lem227458 m) (@lem227457 m)). Qed.
Lemma lem227460 (m : nat) (n : nat) : term39 m n.
Proof. exact (@lem227459 m n). Qed.
Lemma lem227461 (m : nat) (n : nat) : (term39 m n) = (term15 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem227462 (m : nat) (n : nat) : term15 m n.
Proof. exact (EQ_MP (@lem227461 m n) (@lem227460 m n)). Qed.
Lemma lem227463 (m : nat) (n : nat) (p : nat) : term40 m n p.
Proof. exact (@lem227462 m n p). Qed.
Lemma lem227464 (m : nat) (n : nat) (p : nat) : (term40 m n p) = ((term11 m n p) = (term10 m n p)).
Proof. exact (eq_refl (term40 m n p)). Qed.
Lemma lem227466 (m : nat) : term41 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem227467 (m : nat) : (term41 m) = (term42 m).
Proof. exact (eq_refl (term41 m)). Qed.
Lemma lem227468 (m : nat) : term42 m.
Proof. exact (EQ_MP (@lem227467 m) (@lem227466 m)). Qed.
Lemma lem227469 (m : nat) (n : nat) : term43 m n.
Proof. exact (@lem227468 m n). Qed.
Lemma lem227470 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (eq_refl (term43 m n)). Qed.
Lemma lem227471 (m : nat) (n : nat) : term44 m n.
Proof. exact (EQ_MP (@lem227470 m n) (@lem227469 m n)). Qed.
Lemma lem227472 (m : nat) (n : nat) (p : nat) : term45 m n p.
Proof. exact (@lem227471 m n p). Qed.
Lemma lem227473 (m : nat) (n : nat) (p : nat) : (term45 m n p) = ((term46 m n p) = (term47 m n p)).
Proof. exact (eq_refl (term45 m n p)). Qed.
Lemma lem227475 (m : nat) : term48 m.
Proof. exact (@lem227456 m). Qed.
Lemma lem227476 (m : nat) : (term48 m) = (term33 m).
Proof. exact (eq_refl (term48 m)). Qed.
Lemma lem227477 (m : nat) : term33 m.
Proof. exact (EQ_MP (@lem227476 m) (@lem227475 m)). Qed.
Lemma lem227478 (m : nat) (n : nat) : term49 m n.
Proof. exact (@lem227477 m n). Qed.
Lemma lem227479 (m : nat) (n : nat) : (term49 m n) = (term29 m n).
Proof. exact (eq_refl (term49 m n)). Qed.
Lemma lem227480 (m : nat) (n : nat) : term29 m n.
Proof. exact (EQ_MP (@lem227479 m n) (@lem227478 m n)). Qed.
Lemma lem227481 (m : nat) (n : nat) (p : nat) : term50 m n p.
Proof. exact (@lem227480 m n p). Qed.
Lemma lem227482 (m : nat) (n : nat) (p : nat) : (term50 m n p) = ((term25 n m p) = (term24 m n p)).
Proof. exact (eq_refl (term50 m n p)). Qed.
Lemma lem227484 {A : Type'} (x : A) : term51 A x.
Proof. exact (@lem317 A x). Qed.
Lemma lem227485 {A : Type'} (x : A) : (term51 A x) = ((x = x) = True).
Proof. exact (eq_refl (term51 A x)). Qed.
Lemma lem227487 (n : nat) (m : nat) (p : nat) : term52 n m p.
Proof. exact (proj2 (@lem83517 n m p)). Qed.
Lemma lem227503 (n : nat) (m : nat) (p : nat) : (term53 m n p) = (term53 n m p).
Proof. exact (proj2 (@lem227487 n m p)). Qed.
Lemma lem227504 (d : nat) (n : nat) (p : nat) : (term53 n d p) = (term53 d n p).
Proof. exact (@lem227503 d n p). Qed.
Lemma lem227514 (d : nat) (n : nat) (p : nat) : (term54 d n p) = (term54 d n p).
Proof. exact (eq_refl (term54 d n p)). Qed.
Lemma lem227515 (d : nat) (n : nat) (p : nat) : ((term53 d n p) = (term53 n d p)) = ((term53 d n p) = (term53 d n p)).
Proof. exact (MK_COMB (@lem227514 d n p) (@lem227504 d n p)). Qed.
Lemma lem227517 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem227485 A x) (@lem227484 A x)). Qed.
Lemma lem227518 (x : nat) : (x = x) = True.
Proof. exact (@lem227517 nat x). Qed.
Lemma lem227519 (d : nat) (n : nat) (p : nat) : ((term53 d n p) = (term53 d n p)) = True.
Proof. exact (@lem227518 (term53 d n p)). Qed.
Lemma lem227520 (n : nat) (d : nat) (p : nat) : ((term53 d n p) = (term53 n d p)) = True.
Proof. exact (TRANS (@lem227515 d n p) (@lem227519 d n p)). Qed.
Lemma lem227521 (n : nat) (d : nat) (p : nat) : True = ((term53 d n p) = (term53 n d p)).
Proof. exact (SYM (@lem227520 n d p)). Qed.
Lemma lem227523 (m : nat) : term55 m.
Proof. exact (@lem220350 m). Qed.
Lemma lem227524 (m : nat) : (term55 m) = (term18 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem227525 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem227524 m) (@lem227523 m)). Qed.
Lemma lem227526 (m : nat) (n : nat) : term56 m n.
Proof. exact (@lem227525 m n). Qed.
Lemma lem227527 (m : nat) (n : nat) : (term56 m n) = (term14 m n).
Proof. exact (eq_refl (term56 m n)). Qed.
Lemma lem227528 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem227527 m n) (@lem227526 m n)). Qed.
Lemma lem227529 (m : nat) (n : nat) (p : nat) : term57 m n p.
Proof. exact (@lem227528 m n p). Qed.
Lemma lem227530 (m : nat) (n : nat) (p : nat) : (term57 m n p) = ((term10 m n p) = (term11 m n p)).
Proof. exact (eq_refl (term57 m n p)). Qed.
Lemma lem227539 : term5.
Proof. exact (EQ_MP (@lem161372) (@lem161369)). Qed.
Lemma lem227540 (m : nat) : term6 m.
Proof. exact (@lem227539 m). Qed.
Lemma lem227541 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem227542 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem227541 m) (@lem227540 m)). Qed.
Lemma lem227543 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem227542 m n). Qed.
Lemma lem227544 (n : nat) (m : nat) : (term8 m n) = ((term9 m n) = m).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem227557 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem227558 (x : nat) (y : nat) : (term59 x y) = (term60 x y).
Proof. exact (@lem227557 (term59 x y)). Qed.
Lemma lem227559 (x : nat) (y : nat) : (term60 x y) = (term59 x y).
Proof. exact (SYM (@lem227558 x y)). Qed.
Lemma lem227560 (x : nat) (y : nat) (h1 : term61 x y) : term61 x y.
Proof. exact (h1). Qed.
Lemma lem227563 (x : nat) (y : nat) (h1 : term62 x y) : term62 x y.
Proof. exact (h1). Qed.
Lemma lem227564 (x : nat) (y : nat) : term63 x y.
Proof. exact (fun h0 : term62 x y => @lem227563 x y h0). Qed.
Lemma lem227565 (x : nat) (y : nat) (h1 : term63 x y) : term63 x y.
Proof. exact (h1). Qed.
Lemma lem227566 (x : nat) (y : nat) (h1 : term62 x y) : term62 x y.
Proof. exact (h1). Qed.
Lemma lem227567 (x : nat) (y : nat) (h1 : term62 x y) (h2 : term63 x y) : term62 x y.
Proof. exact (@lem227565 x y h2 (@lem227566 x y h1)). Qed.
Lemma lem227568 (x : nat) (y : nat) (h1 : term62 x y) : term64 x y.
Proof. exact (fun h0 : term63 x y => @lem227567 x y h1 h0). Qed.
Lemma lem227569 (x : nat) (y : nat) (h1 : term63 x y) : term63 x y.
Proof. exact (h1). Qed.
Lemma lem227570 (x : nat) (y : nat) (h1 : term62 x y) (h2 : term63 x y) : term62 x y.
Proof. exact (@lem227568 x y h1 (@lem227569 x y h2)). Qed.
Lemma lem227571 (x : nat) (y : nat) (h1 : term63 x y) : term63 x y.
Proof. exact (fun h0 : term62 x y => @lem227570 x y h0 h1). Qed.
Lemma lem227572 (x : nat) (y : nat) : term65 x y.
Proof. exact (fun h0 : term63 x y => @lem227571 x y h0). Qed.
Lemma lem227575 (x : nat) (y : nat) : term63 x y.
Proof. exact (@lem227572 x y (@lem227564 x y)). Qed.
Lemma lem227593 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem227594 : term66 = term67.
Proof. exact (@lem227593 term68). Qed.
Lemma lem227607 (x : nat) (y : nat) : (term69 x y) = (term69 x y).
Proof. exact (eq_refl (term69 x y)). Qed.
Lemma lem227608 (x : nat) (y : nat) : (term62 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem227607 x y) (@lem227594)). Qed.
Lemma lem227611 (y : nat) : (term71 y) = (term72 y).
Proof. exact (fun_ext (fun x : nat => @lem227608 x y)). Qed.
Lemma lem227612 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227613 (y : nat) : (term73 y) = (term74 y).
Proof. exact (MK_COMB (@lem227612) (@lem227611 y)). Qed.
Lemma lem227618 : term75 = term76.
Proof. exact (fun_ext (fun y : nat => @lem227613 y)). Qed.
Lemma lem227619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227628 : term77 = term78.
Proof. exact (MK_COMB (@lem227619) (@lem227618)). Qed.
Lemma lem227633 (m : nat) (n : nat) (p : nat) : (((Nat.add m n) = (Nat.add m p)) = (n = p)) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (((Nat.add m n) = (Nat.add m p)) = (n = p))). Qed.
Lemma lem227634 (m : nat) (n : nat) : (term79 m n) = (term79 m n).
Proof. exact (fun_ext (fun p : nat => @lem227633 m n p)). Qed.
Lemma lem227635 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227636 (m : nat) (n : nat) : (term80 m n) = (term80 m n).
Proof. exact (MK_COMB (@lem227635) (@lem227634 m n)). Qed.
Lemma lem227637 (m : nat) : (term81 m) = (term81 m).
Proof. exact (fun_ext (fun n : nat => @lem227636 m n)). Qed.
Lemma lem227638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227639 (m : nat) : (term82 m) = (term82 m).
Proof. exact (MK_COMB (@lem227638) (@lem227637 m)). Qed.
Lemma lem227640 : term83 = term83.
Proof. exact (fun_ext (fun m : nat => @lem227639 m)). Qed.
Lemma lem227641 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227642 : term68 = term68.
Proof. exact (MK_COMB (@lem227641) (@lem227640)). Qed.
Lemma lem227643 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem227644 : term67 = term67.
Proof. exact (MK_COMB (@lem227643) (@lem227642)). Qed.
Lemma lem227645 (x : nat) (y : nat) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem227646 (x : nat) (a : nat) (y : nat) : ((Nat.add a x) = (Nat.add a y)) = ((Nat.add a x) = (Nat.add a y)).
Proof. exact (eq_refl ((Nat.add a x) = (Nat.add a y))). Qed.
Lemma lem227647 (x : nat) (y : nat) : (term84 x y) = (term84 x y).
Proof. exact (fun_ext (fun a : nat => @lem227646 x a y)). Qed.
Lemma lem227648 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem227649 (x : nat) (y : nat) : (term85 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem227648) (@lem227647 x y)). Qed.
Lemma lem227650 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem227651 (x : nat) (y : nat) : (term86 x y) = (term86 x y).
Proof. exact (MK_COMB (@lem227650) (@lem227649 x y)). Qed.
Lemma lem227652 (x : nat) (y : nat) : (term59 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem227651 x y) (@lem227645 x y)). Qed.
Lemma lem227653 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem227654 (x : nat) (y : nat) : (term61 x y) = (term61 x y).
Proof. exact (MK_COMB (@lem227653) (@lem227652 x y)). Qed.
Lemma lem227655 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem227656 (x : nat) (y : nat) : (term69 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem227655) (@lem227654 x y)). Qed.
Lemma lem227657 (x : nat) (y : nat) : (term70 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem227656 x y) (@lem227644)). Qed.
Lemma lem227658 (y : nat) : (term72 y) = (term72 y).
Proof. exact (fun_ext (fun x : nat => @lem227657 x y)). Qed.
Lemma lem227659 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227660 (y : nat) : (term74 y) = (term74 y).
Proof. exact (MK_COMB (@lem227659) (@lem227658 y)). Qed.
Lemma lem227661 : term76 = term76.
Proof. exact (fun_ext (fun y : nat => @lem227660 y)). Qed.
Lemma lem227662 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227663 : term78 = term78.
Proof. exact (MK_COMB (@lem227662) (@lem227661)). Qed.
Lemma lem227706 : term77 = term78.
Proof. exact (TRANS (@lem227628) (@lem227663)). Qed.
Lemma lem227707 : term78 = term77.
Proof. exact (SYM (@lem227706)). Qed.
Lemma lem227708 (x : nat) (y : nat) (h1 : term61 x y) : term61 x y.
Proof. exact (h1). Qed.
Lemma lem227709 (h1 : term68) : term68.
Proof. exact (h1). Qed.
Lemma lem227710 (x : nat) (a : nat) (y : nat) : ((Nat.add a x) = (Nat.add a y)) = ((Nat.add a x) = (Nat.add a y)).
Proof. exact (eq_refl ((Nat.add a x) = (Nat.add a y))). Qed.
Lemma lem227711 (x : nat) (y : nat) : (term84 x y) = (term84 x y).
Proof. exact (fun_ext (fun a : nat => @lem227710 x a y)). Qed.
Lemma lem227712 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem227713 (x : nat) (y : nat) : (term85 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem227712) (@lem227711 x y)). Qed.
Lemma lem227714 (x : nat) (y : nat) : (term87 x y) = (term87 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem227715 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227716 (x : nat) (y : nat) : (term88 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem227715) (@lem227713 x y)). Qed.
Lemma lem227717 (x : nat) (y : nat) : (term89 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem227716 x y) (@lem227714 x y)). Qed.
Lemma lem227718 (x : nat) (y : nat) : (term61 x y) = (term89 x y).
Proof. exact (@lem17362 (term85 x y) (x = y)). Qed.
Lemma lem227719 (x : nat) (y : nat) : (term61 x y) = (term89 x y).
Proof. exact (TRANS (@lem227718 x y) (@lem227717 x y)). Qed.
Lemma lem227726 {A : Type'} (P : A -> Prop) (Q : Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem227727 (P : nat -> Prop) (Q : Prop) : (term92 P Q) = (term93 P Q).
Proof. exact (@lem227726 nat P Q). Qed.
Lemma lem227728 (x : nat) (y : nat) : (term94 x y) = (term95 x y).
Proof. exact (@lem227727 (term84 x y) (term87 x y)). Qed.
Lemma lem227729 (x : nat) (a : nat) (y : nat) : (term96 x y a) = ((Nat.add a x) = (Nat.add a y)).
Proof. exact (eq_refl (term96 x y a)). Qed.
Lemma lem227730 (x : nat) (y : nat) : (term97 x y) = (term84 x y).
Proof. exact (fun_ext (fun a : nat => @lem227729 x a y)). Qed.
Lemma lem227731 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem227732 (x : nat) (y : nat) : (term98 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem227731) (@lem227730 x y)). Qed.
Lemma lem227733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227734 (x : nat) (y : nat) : (term99 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem227733) (@lem227732 x y)). Qed.
Lemma lem227735 (x : nat) (y : nat) : (term87 x y) = (term87 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem227736 (x : nat) (y : nat) : (term94 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem227734 x y) (@lem227735 x y)). Qed.
Lemma lem227737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem227738 (x : nat) (y : nat) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem227737) (@lem227736 x y)). Qed.
Lemma lem227739 (x : nat) (a : nat) (y : nat) : (term96 x y a) = ((Nat.add a x) = (Nat.add a y)).
Proof. exact (eq_refl (term96 x y a)). Qed.
Lemma lem227740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227741 (x : nat) (a : nat) (y : nat) : (term102 x y a) = (term103 x a y).
Proof. exact (MK_COMB (@lem227740) (@lem227739 x a y)). Qed.
Lemma lem227742 (x : nat) (y : nat) : (term87 x y) = (term87 x y).
Proof. exact (eq_refl (term87 x y)). Qed.
Lemma lem227743 (a : nat) (x : nat) (y : nat) : (term104 a x y) = (term105 a x y).
Proof. exact (MK_COMB (@lem227741 x a y) (@lem227742 x y)). Qed.
Lemma lem227744 (x : nat) (y : nat) : (term106 x y) = (term107 x y).
Proof. exact (fun_ext (fun a : nat => @lem227743 a x y)). Qed.
Lemma lem227745 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem227746 (x : nat) (y : nat) : (term95 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem227745) (@lem227744 x y)). Qed.
Lemma lem227747 (x : nat) (y : nat) : ((term94 x y) = (term95 x y)) = ((term89 x y) = (term108 x y)).
Proof. exact (MK_COMB (@lem227738 x y) (@lem227746 x y)). Qed.
Lemma lem227749 (x : nat) (y : nat) : (term89 x y) = (term108 x y).
Proof. exact (EQ_MP (@lem227747 x y) (@lem227728 x y)). Qed.
Lemma lem227750 (x : nat) (y : nat) : (term61 x y) = (term108 x y).
Proof. exact (TRANS (@lem227719 x y) (@lem227749 x y)). Qed.
Lemma lem227751 (x : nat) (y : nat) (h1 : term61 x y) : term108 x y.
Proof. exact (EQ_MP (@lem227750 x y) (@lem227708 x y h1)). Qed.
Lemma lem227766 (m : nat) (n : nat) (p : nat) : (((Nat.add m n) = (Nat.add m p)) = (n = p)) = (term109 m n p).
Proof. exact (@lem17784 ((Nat.add m n) = (Nat.add m p)) (n = p)). Qed.
Lemma lem227767 (m : nat) (n : nat) : (term79 m n) = (term110 m n).
Proof. exact (fun_ext (fun p : nat => @lem227766 m n p)). Qed.
Lemma lem227768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227769 (m : nat) (n : nat) : (term80 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem227768) (@lem227767 m n)). Qed.
Lemma lem227770 (m : nat) : (term81 m) = (term112 m).
Proof. exact (fun_ext (fun n : nat => @lem227769 m n)). Qed.
Lemma lem227771 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227772 (m : nat) : (term82 m) = (term113 m).
Proof. exact (MK_COMB (@lem227771) (@lem227770 m)). Qed.
Lemma lem227773 : term83 = term114.
Proof. exact (fun_ext (fun m : nat => @lem227772 m)). Qed.
Lemma lem227774 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227775 : term68 = term115.
Proof. exact (MK_COMB (@lem227774) (@lem227773)). Qed.
Lemma lem227785 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem227786 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem227785 nat P Q). Qed.
Lemma lem227787 (m : nat) (n : nat) : (term120 m n) = (term121 m n).
Proof. exact (@lem227786 (term122 m n) (term123 m n)). Qed.
Lemma lem227788 (m : nat) (n : nat) (p : nat) : (term124 m n p) = (term125 m n p).
Proof. exact (eq_refl (term124 m n p)). Qed.
Lemma lem227789 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227790 (m : nat) (n : nat) (p : nat) : (term126 m n p) = (term127 m n p).
Proof. exact (MK_COMB (@lem227789) (@lem227788 m n p)). Qed.
Lemma lem227791 (m : nat) (n : nat) (p : nat) : (term128 m n p) = (term129 m n p).
Proof. exact (eq_refl (term128 m n p)). Qed.
Lemma lem227792 (m : nat) (n : nat) (p : nat) : (term130 m n p) = (term109 m n p).
Proof. exact (MK_COMB (@lem227790 m n p) (@lem227791 m n p)). Qed.
Lemma lem227793 (m : nat) (n : nat) : (term131 m n) = (term110 m n).
Proof. exact (fun_ext (fun p : nat => @lem227792 m n p)). Qed.
Lemma lem227794 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227795 (m : nat) (n : nat) : (term120 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem227794) (@lem227793 m n)). Qed.
Lemma lem227796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem227797 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (MK_COMB (@lem227796) (@lem227795 m n)). Qed.
Lemma lem227798 (m : nat) (n : nat) (p : nat) : (term124 m n p) = (term125 m n p).
Proof. exact (eq_refl (term124 m n p)). Qed.
Lemma lem227799 (m : nat) (n : nat) : (term134 m n) = (term122 m n).
Proof. exact (fun_ext (fun p : nat => @lem227798 m n p)). Qed.
Lemma lem227800 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227801 (m : nat) (n : nat) : (term135 m n) = (term136 m n).
Proof. exact (MK_COMB (@lem227800) (@lem227799 m n)). Qed.
Lemma lem227802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227803 (m : nat) (n : nat) : (term137 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem227802) (@lem227801 m n)). Qed.
Lemma lem227804 (m : nat) (n : nat) (p : nat) : (term128 m n p) = (term129 m n p).
Proof. exact (eq_refl (term128 m n p)). Qed.
Lemma lem227805 (m : nat) (n : nat) : (term139 m n) = (term123 m n).
Proof. exact (fun_ext (fun p : nat => @lem227804 m n p)). Qed.
Lemma lem227806 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227807 (m : nat) (n : nat) : (term140 m n) = (term141 m n).
Proof. exact (MK_COMB (@lem227806) (@lem227805 m n)). Qed.
Lemma lem227808 (m : nat) (n : nat) : (term121 m n) = (term142 m n).
Proof. exact (MK_COMB (@lem227803 m n) (@lem227807 m n)). Qed.
Lemma lem227809 (m : nat) (n : nat) : ((term120 m n) = (term121 m n)) = ((term111 m n) = (term142 m n)).
Proof. exact (MK_COMB (@lem227797 m n) (@lem227808 m n)). Qed.
Lemma lem227810 (m : nat) (n : nat) : (term111 m n) = (term142 m n).
Proof. exact (EQ_MP (@lem227809 m n) (@lem227787 m n)). Qed.
Lemma lem227907 (m : nat) : (term112 m) = (term143 m).
Proof. exact (fun_ext (fun n : nat => @lem227810 m n)). Qed.
Lemma lem227908 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227909 (m : nat) : (term113 m) = (term144 m).
Proof. exact (MK_COMB (@lem227908) (@lem227907 m)). Qed.
Lemma lem227911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem227912 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem227911 nat P Q). Qed.
Lemma lem227913 (m : nat) : (term145 m) = (term146 m).
Proof. exact (@lem227912 (term147 m) (term148 m)). Qed.
Lemma lem227914 (m : nat) (n : nat) : (term149 m n) = (term136 m n).
Proof. exact (eq_refl (term149 m n)). Qed.
Lemma lem227915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227916 (m : nat) (n : nat) : (term150 m n) = (term138 m n).
Proof. exact (MK_COMB (@lem227915) (@lem227914 m n)). Qed.
Lemma lem227917 (m : nat) (n : nat) : (term151 m n) = (term141 m n).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem227918 (m : nat) (n : nat) : (term152 m n) = (term142 m n).
Proof. exact (MK_COMB (@lem227916 m n) (@lem227917 m n)). Qed.
Lemma lem227919 (m : nat) : (term153 m) = (term143 m).
Proof. exact (fun_ext (fun n : nat => @lem227918 m n)). Qed.
Lemma lem227920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227921 (m : nat) : (term145 m) = (term144 m).
Proof. exact (MK_COMB (@lem227920) (@lem227919 m)). Qed.
Lemma lem227922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem227923 (m : nat) : (term154 m) = (term155 m).
Proof. exact (MK_COMB (@lem227922) (@lem227921 m)). Qed.
Lemma lem227924 (m : nat) (n : nat) : (term149 m n) = (term136 m n).
Proof. exact (eq_refl (term149 m n)). Qed.
Lemma lem227925 (m : nat) : (term156 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem227924 m n)). Qed.
Lemma lem227926 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227927 (m : nat) : (term157 m) = (term158 m).
Proof. exact (MK_COMB (@lem227926) (@lem227925 m)). Qed.
Lemma lem227928 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem227929 (m : nat) : (term159 m) = (term160 m).
Proof. exact (MK_COMB (@lem227928) (@lem227927 m)). Qed.
Lemma lem227930 (m : nat) (n : nat) : (term151 m n) = (term141 m n).
Proof. exact (eq_refl (term151 m n)). Qed.
Lemma lem227931 (m : nat) : (term161 m) = (term148 m).
Proof. exact (fun_ext (fun n : nat => @lem227930 m n)). Qed.
Lemma lem227932 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem227933 (m : nat) : (term162 m) = (term163 m).
Proof. exact (MK_COMB (@lem227932) (@lem227931 m)). Qed.
Lemma lem227934 (m : nat) : (term146 m) = (term164 m).
Proof. exact (MK_COMB (@lem227929 m) (@lem227933 m)). Qed.
Lemma lem227935 (m : nat) : ((term145 m) = (term146 m)) = ((term144 m) = (term164 m)).
Proof. exact (MK_COMB (@lem227923 m) (@lem227934 m)). Qed.
Lemma lem227936 (m : nat) : (term144 m) = (term164 m).
Proof. exact (EQ_MP (@lem227935 m) (@lem227913 m)). Qed.
Lemma lem228041 (m : nat) : (term113 m) = (term164 m).
Proof. exact (TRANS (@lem227909 m) (@lem227936 m)). Qed.
Lemma lem228042 : term114 = term165.
Proof. exact (fun_ext (fun m : nat => @lem228041 m)). Qed.
Lemma lem228043 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228044 : term115 = term166.
Proof. exact (MK_COMB (@lem228043) (@lem228042)). Qed.
Lemma lem228046 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term116 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem228047 (P : nat -> Prop) (Q : nat -> Prop) : (term118 P Q) = (term119 P Q).
Proof. exact (@lem228046 nat P Q). Qed.
Lemma lem228048 : term167 = term168.
Proof. exact (@lem228047 term169 term170). Qed.
Lemma lem228049 (m : nat) : (term171 m) = (term158 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem228050 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem228051 (m : nat) : (term172 m) = (term160 m).
Proof. exact (MK_COMB (@lem228050) (@lem228049 m)). Qed.
Lemma lem228052 (m : nat) : (term173 m) = (term163 m).
Proof. exact (eq_refl (term173 m)). Qed.
Lemma lem228053 (m : nat) : (term174 m) = (term164 m).
Proof. exact (MK_COMB (@lem228051 m) (@lem228052 m)). Qed.
Lemma lem228054 : term175 = term165.
Proof. exact (fun_ext (fun m : nat => @lem228053 m)). Qed.
Lemma lem228055 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228056 : term167 = term166.
Proof. exact (MK_COMB (@lem228055) (@lem228054)). Qed.
Lemma lem228057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem228058 : term176 = term177.
Proof. exact (MK_COMB (@lem228057) (@lem228056)). Qed.
Lemma lem228059 (m : nat) : (term171 m) = (term158 m).
Proof. exact (eq_refl (term171 m)). Qed.
Lemma lem228060 : term178 = term169.
Proof. exact (fun_ext (fun m : nat => @lem228059 m)). Qed.
Lemma lem228061 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228062 : term179 = term180.
Proof. exact (MK_COMB (@lem228061) (@lem228060)). Qed.
Lemma lem228063 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem228064 : term181 = term182.
Proof. exact (MK_COMB (@lem228063) (@lem228062)). Qed.
Lemma lem228065 (m : nat) : (term173 m) = (term163 m).
Proof. exact (eq_refl (term173 m)). Qed.
Lemma lem228066 : term183 = term170.
Proof. exact (fun_ext (fun m : nat => @lem228065 m)). Qed.
Lemma lem228067 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228068 : term184 = term185.
Proof. exact (MK_COMB (@lem228067) (@lem228066)). Qed.
Lemma lem228069 : term168 = term186.
Proof. exact (MK_COMB (@lem228064) (@lem228068)). Qed.
Lemma lem228070 : (term167 = term168) = (term166 = term186).
Proof. exact (MK_COMB (@lem228058) (@lem228069)). Qed.
Lemma lem228071 : term166 = term186.
Proof. exact (EQ_MP (@lem228070) (@lem228048)). Qed.
Lemma lem228186 : term115 = term186.
Proof. exact (TRANS (@lem228044) (@lem228071)). Qed.
Lemma lem228187 : term68 = term186.
Proof. exact (TRANS (@lem227775) (@lem228186)). Qed.
Lemma lem228188 (h1 : term68) : term186.
Proof. exact (EQ_MP (@lem228187) (@lem227709 h1)). Qed.
Lemma lem228212 (m : nat) (n : nat) (p : nat) : (term129 m n p) = (term129 m n p).
Proof. exact (eq_refl (term129 m n p)). Qed.
Lemma lem228213 (m : nat) (n : nat) : (term123 m n) = (term123 m n).
Proof. exact (fun_ext (fun p : nat => @lem228212 m n p)). Qed.
Lemma lem228214 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228215 (m : nat) (n : nat) : (term141 m n) = (term141 m n).
Proof. exact (MK_COMB (@lem228214) (@lem228213 m n)). Qed.
Lemma lem228216 (m : nat) : (term148 m) = (term148 m).
Proof. exact (fun_ext (fun n : nat => @lem228215 m n)). Qed.
Lemma lem228217 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228218 (m : nat) : (term163 m) = (term163 m).
Proof. exact (MK_COMB (@lem228217) (@lem228216 m)). Qed.
Lemma lem228219 : term170 = term170.
Proof. exact (fun_ext (fun m : nat => @lem228218 m)). Qed.
Lemma lem228220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228221 : term185 = term185.
Proof. exact (MK_COMB (@lem228220) (@lem228219)). Qed.
Lemma lem228244 (m : nat) (n : nat) (p : nat) : (term125 m n p) = (term125 m n p).
Proof. exact (eq_refl (term125 m n p)). Qed.
Lemma lem228245 (m : nat) (n : nat) : (term122 m n) = (term122 m n).
Proof. exact (fun_ext (fun p : nat => @lem228244 m n p)). Qed.
Lemma lem228246 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228247 (m : nat) (n : nat) : (term136 m n) = (term136 m n).
Proof. exact (MK_COMB (@lem228246) (@lem228245 m n)). Qed.
Lemma lem228248 (m : nat) : (term147 m) = (term147 m).
Proof. exact (fun_ext (fun n : nat => @lem228247 m n)). Qed.
Lemma lem228249 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228250 (m : nat) : (term158 m) = (term158 m).
Proof. exact (MK_COMB (@lem228249) (@lem228248 m)). Qed.
Lemma lem228251 : term169 = term169.
Proof. exact (fun_ext (fun m : nat => @lem228250 m)). Qed.
Lemma lem228252 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228253 : term180 = term180.
Proof. exact (MK_COMB (@lem228252) (@lem228251)). Qed.
Lemma lem228254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem228255 : term182 = term182.
Proof. exact (MK_COMB (@lem228254) (@lem228253)). Qed.
Lemma lem228256 : term186 = term186.
Proof. exact (MK_COMB (@lem228255) (@lem228221)). Qed.
Lemma lem228257 (h1 : term68) : term186.
Proof. exact (EQ_MP (@lem228256) (@lem228188 h1)). Qed.
Lemma lem228281 (a : nat) (x : nat) (y : nat) (h1 : term105 a x y) : term105 a x y.
Proof. exact (h1). Qed.
Lemma lem228284 (h1 : term68) : term185.
Proof. exact (proj2 (@lem228257 h1)). Qed.
Lemma lem228320 (m : nat) (n : nat) (p : nat) : (term129 m n p) = (term129 m n p).
Proof. exact (eq_refl (term129 m n p)). Qed.
Lemma lem228321 (m : nat) (n : nat) : (term123 m n) = (term123 m n).
Proof. exact (fun_ext (fun p : nat => @lem228320 m n p)). Qed.
Lemma lem228322 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228323 (m : nat) (n : nat) : (term141 m n) = (term141 m n).
Proof. exact (MK_COMB (@lem228322) (@lem228321 m n)). Qed.
Lemma lem228324 (m : nat) : (term148 m) = (term148 m).
Proof. exact (fun_ext (fun n : nat => @lem228323 m n)). Qed.
Lemma lem228325 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228326 (m : nat) : (term163 m) = (term163 m).
Proof. exact (MK_COMB (@lem228325) (@lem228324 m)). Qed.
Lemma lem228327 : term170 = term170.
Proof. exact (fun_ext (fun m : nat => @lem228326 m)). Qed.
Lemma lem228328 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228330 : term185 = term185.
Proof. exact (MK_COMB (@lem228328) (@lem228327)). Qed.
Lemma lem228331 (h1 : term68) : term185.
Proof. exact (EQ_MP (@lem228330) (@lem228284 h1)). Qed.
Lemma lem228341 (_4549 : nat) (h1 : term68) : term173 _4549.
Proof. exact (@lem228331 h1 _4549). Qed.
Lemma lem228342 (_4549 : nat) : (term173 _4549) = (term163 _4549).
Proof. exact (eq_refl (term173 _4549)). Qed.
Lemma lem228343 (_4549 : nat) (h1 : term68) : term163 _4549.
Proof. exact (EQ_MP (@lem228342 _4549) (@lem228341 _4549 h1)). Qed.
Lemma lem228344 (_4549 : nat) (_4550 : nat) (h1 : term68) : term151 _4549 _4550.
Proof. exact (@lem228343 _4549 h1 _4550). Qed.
Lemma lem228345 (_4549 : nat) (_4550 : nat) : (term151 _4549 _4550) = (term141 _4549 _4550).
Proof. exact (eq_refl (term151 _4549 _4550)). Qed.
Lemma lem228346 (_4549 : nat) (_4550 : nat) (h1 : term68) : term141 _4549 _4550.
Proof. exact (EQ_MP (@lem228345 _4549 _4550) (@lem228344 _4549 _4550 h1)). Qed.
Lemma lem228347 (_4549 : nat) (_4550 : nat) (_4551 : nat) (h1 : term68) : term128 _4549 _4550 _4551.
Proof. exact (@lem228346 _4549 _4550 h1 _4551). Qed.
Lemma lem228348 (_4549 : nat) (_4550 : nat) (_4551 : nat) : (term128 _4549 _4550 _4551) = (term129 _4549 _4550 _4551).
Proof. exact (eq_refl (term128 _4549 _4550 _4551)). Qed.
Lemma lem228353 (a : nat) (x : nat) (y : nat) (h1 : term105 a x y) : term87 x y.
Proof. exact (proj2 (@lem228281 a x y h1)). Qed.
Lemma lem228365 (_4549 : nat) (_4550 : nat) (_4551 : nat) (h1 : term68) : term129 _4549 _4550 _4551.
Proof. exact (EQ_MP (@lem228348 _4549 _4550 _4551) (@lem228347 _4549 _4550 _4551 h1)). Qed.
Lemma lem228384 (a : nat) (x : nat) (y : nat) (h1 : term105 a x y) : (Nat.add a x) = (Nat.add a y).
Proof. exact (proj1 (@lem228281 a x y h1)). Qed.
Lemma lem228385 (a : nat) (x : nat) (y : nat) (h1 : term105 a x y) : term187 x a y.
Proof. exact (fun h0 : term188 x a y => @lem228384 a x y h1). Qed.
Lemma lem228387 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem228388 (x : nat) (a : nat) (y : nat) : (term187 x a y) = ((Nat.add a x) = (Nat.add a y)).
Proof. exact (@lem228387 ((Nat.add a x) = (Nat.add a y))). Qed.
Lemma lem228389 (a : nat) (x : nat) (y : nat) (h1 : term105 a x y) : (Nat.add a x) = (Nat.add a y).
Proof. exact (EQ_MP (@lem228388 x a y) (@lem228385 a x y h1)). Qed.
Lemma lem228395 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem228396 (_4550 : nat) (_4549 : nat) (_4551 : nat) : (term129 _4549 _4550 _4551) = (term190 _4550 _4549 _4551).
Proof. exact (@lem228395 (_4550 = _4551) (term188 _4550 _4549 _4551)). Qed.
Lemma lem228406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem228407 (_4550 : nat) (_4549 : nat) (_4551 : nat) : (term191 _4549 _4550 _4551) = (term192 _4550 _4549 _4551).
Proof. exact (MK_COMB (@lem228406) (@lem228396 _4550 _4549 _4551)). Qed.
Lemma lem228417 (_4550 : nat) (_4549 : nat) (_4551 : nat) : (term190 _4550 _4549 _4551) = (term190 _4550 _4549 _4551).
Proof. exact (eq_refl (term190 _4550 _4549 _4551)). Qed.
Lemma lem228418 (_4550 : nat) (_4549 : nat) (_4551 : nat) : ((term129 _4549 _4550 _4551) = (term190 _4550 _4549 _4551)) = ((term190 _4550 _4549 _4551) = (term190 _4550 _4549 _4551)).
Proof. exact (MK_COMB (@lem228407 _4550 _4549 _4551) (@lem228417 _4550 _4549 _4551)). Qed.
Lemma lem228420 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem228421 (x : Prop) : (x = x) = True.
Proof. exact (@lem228420 Prop x). Qed.
Lemma lem228422 (_4550 : nat) (_4549 : nat) (_4551 : nat) : ((term190 _4550 _4549 _4551) = (term190 _4550 _4549 _4551)) = True.
Proof. exact (@lem228421 (term190 _4550 _4549 _4551)). Qed.
Lemma lem228423 (_4550 : nat) (_4549 : nat) (_4551 : nat) : ((term129 _4549 _4550 _4551) = (term190 _4550 _4549 _4551)) = True.
Proof. exact (TRANS (@lem228418 _4550 _4549 _4551) (@lem228422 _4550 _4549 _4551)). Qed.
Lemma lem228424 (_4550 : nat) (_4549 : nat) (_4551 : nat) : True = ((term129 _4549 _4550 _4551) = (term190 _4550 _4549 _4551)).
Proof. exact (SYM (@lem228423 _4550 _4549 _4551)). Qed.
Lemma lem228425 (_4550 : nat) (_4549 : nat) (_4551 : nat) : (term129 _4549 _4550 _4551) = (term190 _4550 _4549 _4551).
Proof. exact (EQ_MP (@lem228424 _4550 _4549 _4551) (@lem0)). Qed.
Lemma lem228426 (_4550 : nat) (_4549 : nat) (_4551 : nat) (h1 : term68) : term190 _4550 _4549 _4551.
Proof. exact (EQ_MP (@lem228425 _4550 _4549 _4551) (@lem228365 _4549 _4550 _4551 h1)). Qed.
Lemma lem228428 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem228429 (_4549 : nat) (_4550 : nat) (_4551 : nat) : (term190 _4550 _4549 _4551) = (term194 _4549 _4550 _4551).
Proof. exact (@lem228428 (term188 _4550 _4549 _4551) (_4550 = _4551)). Qed.
Lemma lem228431 (a : Prop) : (term195 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem228432 (_4550 : nat) (_4549 : nat) (_4551 : nat) : (term196 _4550 _4549 _4551) = ((Nat.add _4549 _4550) = (Nat.add _4549 _4551)).
Proof. exact (@lem228431 ((Nat.add _4549 _4550) = (Nat.add _4549 _4551))). Qed.
Lemma lem228433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem228434 (_4550 : nat) (_4549 : nat) (_4551 : nat) : (term197 _4550 _4549 _4551) = (term198 _4550 _4549 _4551).
Proof. exact (MK_COMB (@lem228433) (@lem228432 _4550 _4549 _4551)). Qed.
Lemma lem228435 (_4550 : nat) (_4551 : nat) : (_4550 = _4551) = (_4550 = _4551).
Proof. exact (eq_refl (_4550 = _4551)). Qed.
Lemma lem228436 (_4549 : nat) (_4550 : nat) (_4551 : nat) : (term194 _4549 _4550 _4551) = (term199 _4549 _4550 _4551).
Proof. exact (MK_COMB (@lem228434 _4550 _4549 _4551) (@lem228435 _4550 _4551)). Qed.
Lemma lem228437 (_4549 : nat) (_4550 : nat) (_4551 : nat) : (term190 _4550 _4549 _4551) = (term199 _4549 _4550 _4551).
Proof. exact (TRANS (@lem228429 _4549 _4550 _4551) (@lem228436 _4549 _4550 _4551)). Qed.
Lemma lem228440 (_4549 : nat) (_4550 : nat) (_4551 : nat) (h1 : term68) : term199 _4549 _4550 _4551.
Proof. exact (EQ_MP (@lem228437 _4549 _4550 _4551) (@lem228426 _4550 _4549 _4551 h1)). Qed.
Lemma lem228441 (a : nat) (x : nat) (y : nat) (h1 : term68) : term199 a x y.
Proof. exact (@lem228440 a x y h1). Qed.
Lemma lem228444 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : x = y.
Proof. exact (@lem228441 a x y h1 (@lem228389 a x y h2)). Qed.
Lemma lem228445 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : term200 x y.
Proof. exact (fun h0 : term87 x y => @lem228444 a x y h1 h2). Qed.
Lemma lem228447 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem228448 (x : nat) (y : nat) : (term200 x y) = (x = y).
Proof. exact (@lem228447 (x = y)). Qed.
Lemma lem228449 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : x = y.
Proof. exact (EQ_MP (@lem228448 x y) (@lem228445 a x y h1 h2)). Qed.
Lemma lem228452 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem228454 (x : nat) (y : nat) : (term87 x y) = (term201 x y).
Proof. exact (@lem228452 (x = y)). Qed.
Lemma lem228457 (a : nat) (x : nat) (y : nat) (h1 : term105 a x y) : term201 x y.
Proof. exact (EQ_MP (@lem228454 x y) (@lem228353 a x y h1)). Qed.
Lemma lem228460 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : False.
Proof. exact (@lem228457 a x y h2 (@lem228449 a x y h1 h2)). Qed.
Lemma lem228461 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : term202.
Proof. exact (fun h0 : ~ False => @lem228460 a x y h1 h2). Qed.
Lemma lem228463 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem228464 : term202 = False.
Proof. exact (@lem228463 False). Qed.
Lemma lem228465 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : False.
Proof. exact (EQ_MP (@lem228464) (@lem228461 a x y h1 h2)). Qed.
Lemma lem228466 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : (term105 a x y) = False.
Proof. exact (prop_ext (fun h3 : term105 a x y => @lem228465 a x y h1 h2) (fun h3 : False => @lem228281 a x y h2)). Qed.
Lemma lem228467 (a : nat) (x : nat) (y : nat) (h1 : term68) (h2 : term105 a x y) : False.
Proof. exact (EQ_MP (@lem228466 a x y h1 h2) (@lem228281 a x y h2)). Qed.
Lemma lem228468 (x : nat) (y : nat) (h1 : term68) (h2 : term61 x y) : False.
Proof. exact (ex_elim (@lem227751 x y h2) (fun a : nat => fun h0 : term107 x y a => @lem228467 a x y h1 h0)). Qed.
Lemma lem228469 (x : nat) (y : nat) (h1 : term61 x y) : term66.
Proof. exact (fun h0 : term68 => @lem228468 x y h0 h1). Qed.
Lemma lem228470 : term66 = term67.
Proof. exact (@lem69 term68). Qed.
Lemma lem228471 (x : nat) (y : nat) (h1 : term61 x y) : term67.
Proof. exact (EQ_MP (@lem228470) (@lem228469 x y h1)). Qed.
Lemma lem228472 (x : nat) (y : nat) : term70 x y.
Proof. exact (fun h0 : term61 x y => @lem228471 x y h0). Qed.
Lemma lem228477 (y : nat) : term74 y.
Proof. exact (fun x : nat => @lem228472 x y). Qed.
Lemma lem228482 : term78.
Proof. exact (fun y : nat => @lem228477 y). Qed.
Lemma lem228483 : term77.
Proof. exact (EQ_MP (@lem227707) (@lem228482)). Qed.
Lemma lem228484 (y : nat) : term203 y.
Proof. exact (@lem228483 y). Qed.
Lemma lem228485 (y : nat) : (term203 y) = (term73 y).
Proof. exact (eq_refl (term203 y)). Qed.
Lemma lem228486 (y : nat) : term73 y.
Proof. exact (EQ_MP (@lem228485 y) (@lem228484 y)). Qed.
Lemma lem228487 (y : nat) (x : nat) : term204 y x.
Proof. exact (@lem228486 y x). Qed.
Lemma lem228488 (x : nat) (y : nat) : (term204 y x) = (term62 x y).
Proof. exact (eq_refl (term204 y x)). Qed.
Lemma lem228489 (x : nat) (y : nat) : term62 x y.
Proof. exact (EQ_MP (@lem228488 x y) (@lem228487 y x)). Qed.
Lemma lem228491 (x : nat) (y : nat) : term62 x y.
Proof. exact (@lem227575 x y (@lem228489 x y)). Qed.
Lemma lem228492 (x : nat) (y : nat) (h1 : term61 x y) : term66.
Proof. exact (@lem228491 x y (@lem227560 x y h1)). Qed.
Lemma lem228493 (x : nat) (y : nat) (h1 : term61 x y) : False.
Proof. exact (@lem228492 x y h1 (@lem79639)). Qed.
Lemma lem228494 (x : nat) (y : nat) (h1 : term61 x y) : (term61 x y) = False.
Proof. exact (prop_ext (fun h2 : term61 x y => @lem228493 x y h1) (fun h2 : False => @lem227560 x y h1)). Qed.
Lemma lem228495 (x : nat) (y : nat) (h1 : term61 x y) : False.
Proof. exact (EQ_MP (@lem228494 x y h1) (@lem227560 x y h1)). Qed.
Lemma lem228496 (x : nat) (y : nat) : term60 x y.
Proof. exact (fun h0 : term61 x y => @lem228495 x y h0). Qed.
Lemma lem228497 (x : nat) (y : nat) : term59 x y.
Proof. exact (EQ_MP (@lem227559 x y) (@lem228496 x y)). Qed.
Lemma lem228498 (x : nat) (y : nat) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem228499 (x : nat) (y : nat) (h1 : term85 x y) : term85 x y.
Proof. exact (h1). Qed.
Lemma lem228500 (x : nat) (y : nat) (h1 : term85 x y) (h2 : term59 x y) : x = y.
Proof. exact (@lem228498 x y h2 (@lem228499 x y h1)). Qed.
Lemma lem228501 (x : nat) (y : nat) (h1 : term85 x y) : term205 x y.
Proof. exact (fun h0 : term59 x y => @lem228500 x y h1 h0). Qed.
Lemma lem228502 (x : nat) (y : nat) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem228503 (x : nat) (y : nat) (h1 : term85 x y) (h2 : term59 x y) : x = y.
Proof. exact (@lem228501 x y h1 (@lem228502 x y h2)). Qed.
Lemma lem228504 (x : nat) (y : nat) (h1 : term59 x y) : term59 x y.
Proof. exact (fun h0 : term85 x y => @lem228503 x y h0 h1). Qed.
Lemma lem228505 (x : nat) (y : nat) : term206 x y.
Proof. exact (fun h0 : term59 x y => @lem228504 x y h0). Qed.
Lemma lem228517 (p : nat) : term207 p.
Proof. exact (@lem9784 (p = (NUMERAL 0))). Qed.
Lemma lem228518 (p : nat) : (term207 p) = (term208 p).
Proof. exact (eq_refl (term207 p)). Qed.
Lemma lem228519 (p : nat) : term208 p.
Proof. exact (EQ_MP (@lem228518 p) (@lem228517 p)). Qed.
Lemma lem228520 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228522 (n : nat) : term207 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem228523 (n : nat) : (term207 n) = (term208 n).
Proof. exact (eq_refl (term207 n)). Qed.
Lemma lem228524 (n : nat) : term208 n.
Proof. exact (EQ_MP (@lem228523 n) (@lem228522 n)). Qed.
Lemma lem228526 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem228547 : term210.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem228548 (n : nat) : term211 n.
Proof. exact (@lem228547 n). Qed.
Lemma lem228549 (n : nat) : (term211 n) = ((term212 n) = n).
Proof. exact (eq_refl (term211 n)). Qed.
Lemma lem228551 (n : nat) : term213 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem228552 (n : nat) : (term213 n) = ((term214 n) = n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem228584 : term215.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem228585 (n : nat) : term216 n.
Proof. exact (@lem228584 n). Qed.
Lemma lem228586 (n : nat) : (term216 n) = ((term217 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term216 n)). Qed.
Lemma lem228591 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228592 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem228593 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term218.
Proof. exact (MK_COMB (@lem228592) (@lem228591 n h1)). Qed.
Lemma lem228594 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem228595 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (term217 p).
Proof. exact (MK_COMB (@lem228593 n h1) (@lem228594 p)). Qed.
Lemma lem228597 (n : nat) : (term217 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem228586 n) (@lem228585 n)). Qed.
Lemma lem228598 (p : nat) : (term217 p) = (NUMERAL 0).
Proof. exact (@lem228597 p). Qed.
Lemma lem228599 (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem228595 p n h1) (@lem228598 p)). Qed.
Lemma lem228600 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem228601 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term219 m n p) = (term214 m).
Proof. exact (MK_COMB (@lem228600 m) (@lem228599 p n h1)). Qed.
Lemma lem228603 (n : nat) : (term214 n) = n.
Proof. exact (EQ_MP (@lem228552 n) (@lem228551 n)). Qed.
Lemma lem228604 (m : nat) : (term214 m) = m.
Proof. exact (@lem228603 m). Qed.
Lemma lem228605 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term219 m n p) = m.
Proof. exact (TRANS (@lem228601 p m n h1) (@lem228604 m)). Qed.
Lemma lem228606 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem228607 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term220 m n p) = (@eq nat m).
Proof. exact (MK_COMB (@lem228606) (@lem228605 p m n h1)). Qed.
Lemma lem228609 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228610 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem228611 (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.mul n) = term218.
Proof. exact (MK_COMB (@lem228610) (@lem228609 n h1)). Qed.
Lemma lem228613 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228614 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem228615 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term221 m).
Proof. exact (MK_COMB (@lem228614 m) (@lem228613 n h1)). Qed.
Lemma lem228616 : Nat.modulo = Nat.modulo.
Proof. exact (eq_refl Nat.modulo). Qed.
Lemma lem228617 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term222 m n) = (term223 m).
Proof. exact (MK_COMB (@lem228616) (@lem228615 m n h1)). Qed.
Lemma lem228618 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem228619 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term224 m n p) = (term225 m p).
Proof. exact (MK_COMB (@lem228617 m n h1) (@lem228618 p)). Qed.
Lemma lem228620 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term226 m n p) = (term227 m p).
Proof. exact (MK_COMB (@lem228611 n h1) (@lem228619 m p n h1)). Qed.
Lemma lem228622 (n : nat) : (term217 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem228586 n) (@lem228585 n)). Qed.
Lemma lem228623 (m : nat) (p : nat) : (term227 m p) = (NUMERAL 0).
Proof. exact (@lem228622 (term225 m p)). Qed.
Lemma lem228624 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term226 m n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem228620 m p n h1) (@lem228623 m p)). Qed.
Lemma lem228625 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem228626 (m : nat) (p : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term228 m n p) = term229.
Proof. exact (MK_COMB (@lem228625) (@lem228624 m p n h1)). Qed.
Lemma lem228628 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228629 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem228630 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term214 m).
Proof. exact (MK_COMB (@lem228629 m) (@lem228628 n h1)). Qed.
Lemma lem228632 (n : nat) : (term214 n) = n.
Proof. exact (EQ_MP (@lem228552 n) (@lem228551 n)). Qed.
Lemma lem228633 (m : nat) : (term214 m) = m.
Proof. exact (@lem228632 m). Qed.
Lemma lem228634 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem228630 m n h1) (@lem228633 m)). Qed.
Lemma lem228635 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term230 p m n) = (term212 m).
Proof. exact (MK_COMB (@lem228626 m p n h1) (@lem228634 m n h1)). Qed.
Lemma lem228637 (n : nat) : (term212 n) = n.
Proof. exact (EQ_MP (@lem228549 n) (@lem228548 n)). Qed.
Lemma lem228638 (m : nat) : (term212 m) = m.
Proof. exact (@lem228637 m). Qed.
Lemma lem228639 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term230 p m n) = m.
Proof. exact (TRANS (@lem228635 p m n h1) (@lem228638 m)). Qed.
Lemma lem228640 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term219 m n p) = (term230 p m n)) = (m = m).
Proof. exact (MK_COMB (@lem228607 p m n h1) (@lem228639 p m n h1)). Qed.
Lemma lem228642 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem228643 (x : nat) : (x = x) = True.
Proof. exact (@lem228642 nat x). Qed.
Lemma lem228644 (m : nat) : (m = m) = True.
Proof. exact (@lem228643 m). Qed.
Lemma lem228645 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term219 m n p) = (term230 p m n)) = True.
Proof. exact (TRANS (@lem228640 p m n h1) (@lem228644 m)). Qed.
Lemma lem228646 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = ((term219 m n p) = (term230 p m n)).
Proof. exact (SYM (@lem228645 p m n h1)). Qed.
Lemma lem228647 (p : nat) (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term219 m n p) = (term230 p m n).
Proof. exact (EQ_MP (@lem228646 p m n h1) (@lem0)). Qed.
Lemma lem228726 (n : nat) : term213 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem228727 (n : nat) : (term213 n) = ((term214 n) = n).
Proof. exact (eq_refl (term213 n)). Qed.
Lemma lem228729 : term231.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem228755 : term232.
Proof. exact (proj1 (@lem228729)). Qed.
Lemma lem228756 (m : nat) : term233 m.
Proof. exact (@lem228755 m). Qed.
Lemma lem228757 (m : nat) : (term233 m) = ((term234 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term233 m)). Qed.
Lemma lem228779 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228780 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem228781 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (term234 n).
Proof. exact (MK_COMB (@lem228780 n) (@lem228779 p h1)). Qed.
Lemma lem228783 (m : nat) : (term234 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem228757 m) (@lem228756 m)). Qed.
Lemma lem228784 (n : nat) : (term234 n) = (NUMERAL 0).
Proof. exact (@lem228783 n). Qed.
Lemma lem228785 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (Nat.mul n p) = (NUMERAL 0).
Proof. exact (TRANS (@lem228781 n p h1) (@lem228784 n)). Qed.
Lemma lem228786 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem228787 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term219 m n p) = (term214 m).
Proof. exact (MK_COMB (@lem228786 m) (@lem228785 n p h1)). Qed.
Lemma lem228789 (n : nat) : (term214 n) = n.
Proof. exact (EQ_MP (@lem228727 n) (@lem228726 n)). Qed.
Lemma lem228790 (m : nat) : (term214 m) = m.
Proof. exact (@lem228789 m). Qed.
Lemma lem228791 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term219 m n p) = m.
Proof. exact (TRANS (@lem228787 n m p h1) (@lem228790 m)). Qed.
Lemma lem228792 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem228793 (n : nat) (m : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term220 m n p) = (@eq nat m).
Proof. exact (MK_COMB (@lem228792) (@lem228791 n m p h1)). Qed.
Lemma lem228795 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem228796 (m : nat) (n : nat) : (term222 m n) = (term222 m n).
Proof. exact (eq_refl (term222 m n)). Qed.
Lemma lem228797 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term224 m n p) = (term235 m n).
Proof. exact (MK_COMB (@lem228796 m n) (@lem228795 p h1)). Qed.
Lemma lem228799 (n : nat) : (term214 n) = n.
Proof. exact (EQ_MP (@lem228727 n) (@lem228726 n)). Qed.
Lemma lem228800 (m : nat) (n : nat) : (term235 m n) = (Nat.div m n).
Proof. exact (@lem228799 (Nat.div m n)). Qed.
Lemma lem228801 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term224 m n p) = (Nat.div m n).
Proof. exact (TRANS (@lem228797 m n p h1) (@lem228800 m n)). Qed.
Lemma lem228802 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem228803 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term226 m n p) = (term236 m n).
Proof. exact (MK_COMB (@lem228802 n) (@lem228801 m n p h1)). Qed.
Lemma lem228804 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem228805 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term228 m n p) = (term237 m n).
Proof. exact (MK_COMB (@lem228804) (@lem228803 m n p h1)). Qed.
Lemma lem228806 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem228807 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (term230 p m n) = (term4 m n).
Proof. exact (MK_COMB (@lem228805 m n p h1) (@lem228806 m n)). Qed.
Lemma lem228808 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : ((term219 m n p) = (term230 p m n)) = (m = (term4 m n)).
Proof. exact (MK_COMB (@lem228793 n m p h1) (@lem228807 m n p h1)). Qed.
Lemma lem228811 (m : nat) (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : (m = (term4 m n)) = ((term219 m n p) = (term230 p m n)).
Proof. exact (SYM (@lem228808 m n p h1)). Qed.
Lemma lem228813 (p : Prop) : p = (term58 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem228814 (m : nat) (n : nat) : (m = (term4 m n)) = (term238 m n).
Proof. exact (@lem228813 (m = (term4 m n))). Qed.
Lemma lem228815 (m : nat) (n : nat) : (term238 m n) = (m = (term4 m n)).
Proof. exact (SYM (@lem228814 m n)). Qed.
Lemma lem228816 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem228819 (p : nat) (m : nat) (n : nat) (h1 : term240 p m n) : term240 p m n.
Proof. exact (h1). Qed.
Lemma lem228820 (p : nat) (m : nat) (n : nat) : term241 p m n.
Proof. exact (fun h0 : term240 p m n => @lem228819 p m n h0). Qed.
Lemma lem228821 (p : nat) (m : nat) (n : nat) (h1 : term241 p m n) : term241 p m n.
Proof. exact (h1). Qed.
Lemma lem228822 (p : nat) (m : nat) (n : nat) (h1 : term240 p m n) : term240 p m n.
Proof. exact (h1). Qed.
Lemma lem228823 (p : nat) (m : nat) (n : nat) (h1 : term240 p m n) (h2 : term241 p m n) : term240 p m n.
Proof. exact (@lem228821 p m n h2 (@lem228822 p m n h1)). Qed.
Lemma lem228824 (p : nat) (m : nat) (n : nat) (h1 : term240 p m n) : term242 p m n.
Proof. exact (fun h0 : term241 p m n => @lem228823 p m n h1 h0). Qed.
Lemma lem228825 (p : nat) (m : nat) (n : nat) (h1 : term241 p m n) : term241 p m n.
Proof. exact (h1). Qed.
Lemma lem228826 (p : nat) (m : nat) (n : nat) (h1 : term240 p m n) (h2 : term241 p m n) : term240 p m n.
Proof. exact (@lem228824 p m n h1 (@lem228825 p m n h2)). Qed.
Lemma lem228827 (p : nat) (m : nat) (n : nat) (h1 : term241 p m n) : term241 p m n.
Proof. exact (fun h0 : term240 p m n => @lem228826 p m n h0 h1). Qed.
Lemma lem228828 (p : nat) (m : nat) (n : nat) : term243 p m n.
Proof. exact (fun h0 : term241 p m n => @lem228827 p m n h0). Qed.
Lemma lem228831 (p : nat) (m : nat) (n : nat) : term241 p m n.
Proof. exact (@lem228828 p m n (@lem228820 p m n)). Qed.
Lemma lem228861 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem228862 : term244 = term245.
Proof. exact (@lem228861 term246). Qed.
Lemma lem228875 : term247 = term247.
Proof. exact (eq_refl term247). Qed.
Lemma lem228876 : term248 = term249.
Proof. exact (MK_COMB (@lem228875) (@lem228862)). Qed.
Lemma lem228879 (m : nat) (n : nat) : (term250 m n) = (term250 m n).
Proof. exact (eq_refl (term250 m n)). Qed.
Lemma lem228880 (m : nat) (n : nat) : (term251 m n) = (term252 m n).
Proof. exact (MK_COMB (@lem228879 m n) (@lem228876)). Qed.
Lemma lem228883 (p : nat) : (term253 p) = (term253 p).
Proof. exact (eq_refl (term253 p)). Qed.
Lemma lem228884 (p : nat) (m : nat) (n : nat) : (term254 p m n) = (term255 p m n).
Proof. exact (MK_COMB (@lem228883 p) (@lem228880 m n)). Qed.
Lemma lem228887 (n : nat) : (term256 n) = (term256 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem228888 (p : nat) (m : nat) (n : nat) : (term240 p m n) = (term257 p m n).
Proof. exact (MK_COMB (@lem228887 n) (@lem228884 p m n)). Qed.
Lemma lem228891 (m : nat) (n : nat) : (term258 m n) = (term259 m n).
Proof. exact (fun_ext (fun p : nat => @lem228888 p m n)). Qed.
Lemma lem228892 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228893 (m : nat) (n : nat) : (term260 m n) = (term261 m n).
Proof. exact (MK_COMB (@lem228892) (@lem228891 m n)). Qed.
Lemma lem228898 (n : nat) : (term262 n) = (term263 n).
Proof. exact (fun_ext (fun m : nat => @lem228893 m n)). Qed.
Lemma lem228899 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228900 (n : nat) : (term264 n) = (term265 n).
Proof. exact (MK_COMB (@lem228899) (@lem228898 n)). Qed.
Lemma lem228905 : term266 = term267.
Proof. exact (fun_ext (fun n : nat => @lem228900 n)). Qed.
Lemma lem228906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228915 : term268 = term269.
Proof. exact (MK_COMB (@lem228906) (@lem228905)). Qed.
Lemma lem228926 (m : nat) (n : nat) : (term270 m n) = (term270 m n).
Proof. exact (eq_refl (term270 m n)). Qed.
Lemma lem228927 (m : nat) : (term271 m) = (term271 m).
Proof. exact (fun_ext (fun n : nat => @lem228926 m n)). Qed.
Lemma lem228928 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228929 (m : nat) : (term272 m) = (term272 m).
Proof. exact (MK_COMB (@lem228928) (@lem228927 m)). Qed.
Lemma lem228930 : term273 = term273.
Proof. exact (fun_ext (fun m : nat => @lem228929 m)). Qed.
Lemma lem228931 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228932 : term246 = term246.
Proof. exact (MK_COMB (@lem228931) (@lem228930)). Qed.
Lemma lem228933 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem228934 : term245 = term245.
Proof. exact (MK_COMB (@lem228933) (@lem228932)). Qed.
Lemma lem228935 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem228936 (m : nat) : (term274 m) = (term274 m).
Proof. exact (fun_ext (fun n : nat => @lem228935 n m)). Qed.
Lemma lem228937 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228938 (m : nat) : (term275 m) = (term275 m).
Proof. exact (MK_COMB (@lem228937) (@lem228936 m)). Qed.
Lemma lem228939 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem228938 m)). Qed.
Lemma lem228940 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228941 : term277 = term277.
Proof. exact (MK_COMB (@lem228940) (@lem228939)). Qed.
Lemma lem228942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem228943 : term247 = term247.
Proof. exact (MK_COMB (@lem228942) (@lem228941)). Qed.
Lemma lem228944 : term249 = term249.
Proof. exact (MK_COMB (@lem228943) (@lem228934)). Qed.
Lemma lem228949 (m : nat) (n : nat) : (term250 m n) = (term250 m n).
Proof. exact (eq_refl (term250 m n)). Qed.
Lemma lem228950 (m : nat) (n : nat) : (term252 m n) = (term252 m n).
Proof. exact (MK_COMB (@lem228949 m n) (@lem228944)). Qed.
Lemma lem228953 (p : nat) : (term253 p) = (term253 p).
Proof. exact (eq_refl (term253 p)). Qed.
Lemma lem228954 (p : nat) (m : nat) (n : nat) : (term255 p m n) = (term255 p m n).
Proof. exact (MK_COMB (@lem228953 p) (@lem228950 m n)). Qed.
Lemma lem228959 (n : nat) : (term256 n) = (term256 n).
Proof. exact (eq_refl (term256 n)). Qed.
Lemma lem228960 (p : nat) (m : nat) (n : nat) : (term257 p m n) = (term257 p m n).
Proof. exact (MK_COMB (@lem228959 n) (@lem228954 p m n)). Qed.
Lemma lem228961 (m : nat) (n : nat) : (term259 m n) = (term259 m n).
Proof. exact (fun_ext (fun p : nat => @lem228960 p m n)). Qed.
Lemma lem228962 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228963 (m : nat) (n : nat) : (term261 m n) = (term261 m n).
Proof. exact (MK_COMB (@lem228962) (@lem228961 m n)). Qed.
Lemma lem228964 (n : nat) : (term263 n) = (term263 n).
Proof. exact (fun_ext (fun m : nat => @lem228963 m n)). Qed.
Lemma lem228965 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228966 (n : nat) : (term265 n) = (term265 n).
Proof. exact (MK_COMB (@lem228965) (@lem228964 n)). Qed.
Lemma lem228967 : term267 = term267.
Proof. exact (fun_ext (fun n : nat => @lem228966 n)). Qed.
Lemma lem228968 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem228969 : term269 = term269.
Proof. exact (MK_COMB (@lem228968) (@lem228967)). Qed.
Lemma lem229026 : term268 = term269.
Proof. exact (TRANS (@lem228915) (@lem228969)). Qed.
Lemma lem229027 : term269 = term268.
Proof. exact (SYM (@lem229026)). Qed.
Lemma lem229031 (h1 : term277) : term277.
Proof. exact (h1). Qed.
Lemma lem229032 (h1 : term246) : term246.
Proof. exact (h1). Qed.
Lemma lem229038 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem229044 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem229050 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem229051 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem229052 (m : nat) : (term274 m) = (term274 m).
Proof. exact (fun_ext (fun n : nat => @lem229051 n m)). Qed.
Lemma lem229053 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229054 (m : nat) : (term275 m) = (term275 m).
Proof. exact (MK_COMB (@lem229053) (@lem229052 m)). Qed.
Lemma lem229055 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem229054 m)). Qed.
Lemma lem229056 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229069 : term277 = term277.
Proof. exact (MK_COMB (@lem229056) (@lem229055)). Qed.
Lemma lem229070 (h1 : term277) : term277.
Proof. exact (EQ_MP (@lem229069) (@lem229031 h1)). Qed.
Lemma lem229073 (n : nat) : (term278 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem229078 (m : nat) (n : nat) : (term279 m n) = (term279 m n).
Proof. exact (eq_refl (term279 m n)). Qed.
Lemma lem229079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem229080 (n : nat) : (term280 n) = (term281 n).
Proof. exact (MK_COMB (@lem229079) (@lem229073 n)). Qed.
Lemma lem229081 (m : nat) (n : nat) : (term282 m n) = (term283 m n).
Proof. exact (MK_COMB (@lem229080 n) (@lem229078 m n)). Qed.
Lemma lem229082 (m : nat) (n : nat) : (term270 m n) = (term282 m n).
Proof. exact (@lem17265 (term209 n) (term279 m n)). Qed.
Lemma lem229083 (m : nat) (n : nat) : (term270 m n) = (term283 m n).
Proof. exact (TRANS (@lem229082 m n) (@lem229081 m n)). Qed.
Lemma lem229084 (m : nat) : (term271 m) = (term284 m).
Proof. exact (fun_ext (fun n : nat => @lem229083 m n)). Qed.
Lemma lem229085 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229086 (m : nat) : (term272 m) = (term285 m).
Proof. exact (MK_COMB (@lem229085) (@lem229084 m)). Qed.
Lemma lem229087 : term273 = term286.
Proof. exact (fun_ext (fun m : nat => @lem229086 m)). Qed.
Lemma lem229088 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229145 : term246 = term287.
Proof. exact (MK_COMB (@lem229088) (@lem229087)). Qed.
Lemma lem229146 (h1 : term246) : term287.
Proof. exact (EQ_MP (@lem229145) (@lem229032 h1)). Qed.
Lemma lem229156 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem229164 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem229188 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem229201 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem229202 (m : nat) : (term274 m) = (term274 m).
Proof. exact (fun_ext (fun n : nat => @lem229201 n m)). Qed.
Lemma lem229203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229204 (m : nat) : (term275 m) = (term275 m).
Proof. exact (MK_COMB (@lem229203) (@lem229202 m)). Qed.
Lemma lem229205 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem229204 m)). Qed.
Lemma lem229206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229207 : term277 = term277.
Proof. exact (MK_COMB (@lem229206) (@lem229205)). Qed.
Lemma lem229208 (h1 : term277) : term277.
Proof. exact (EQ_MP (@lem229207) (@lem229070 h1)). Qed.
Lemma lem229251 (m : nat) (n : nat) : (term283 m n) = (term283 m n).
Proof. exact (eq_refl (term283 m n)). Qed.
Lemma lem229252 (m : nat) : (term284 m) = (term284 m).
Proof. exact (fun_ext (fun n : nat => @lem229251 m n)). Qed.
Lemma lem229253 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229254 (m : nat) : (term285 m) = (term285 m).
Proof. exact (MK_COMB (@lem229253) (@lem229252 m)). Qed.
Lemma lem229255 : term286 = term286.
Proof. exact (fun_ext (fun m : nat => @lem229254 m)). Qed.
Lemma lem229256 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229257 : term287 = term287.
Proof. exact (MK_COMB (@lem229256) (@lem229255)). Qed.
Lemma lem229258 (h1 : term246) : term287.
Proof. exact (EQ_MP (@lem229257) (@lem229146 h1)). Qed.
Lemma lem229262 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem229266 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem229270 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem229272 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem229273 (m : nat) : (term274 m) = (term274 m).
Proof. exact (fun_ext (fun n : nat => @lem229272 n m)). Qed.
Lemma lem229274 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229275 (m : nat) : (term275 m) = (term275 m).
Proof. exact (MK_COMB (@lem229274) (@lem229273 m)). Qed.
Lemma lem229276 : term276 = term276.
Proof. exact (fun_ext (fun m : nat => @lem229275 m)). Qed.
Lemma lem229277 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229279 : term277 = term277.
Proof. exact (MK_COMB (@lem229277) (@lem229276)). Qed.
Lemma lem229280 (h1 : term277) : term277.
Proof. exact (EQ_MP (@lem229279) (@lem229208 h1)). Qed.
Lemma lem229298 (m : nat) (n : nat) : (term283 m n) = (term288 m n).
Proof. exact (@lem19490 (m = (term9 m n)) (n = (NUMERAL 0)) (term289 m n)). Qed.
Lemma lem229299 (m : nat) : (term284 m) = (term290 m).
Proof. exact (fun_ext (fun n : nat => @lem229298 m n)). Qed.
Lemma lem229300 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229301 (m : nat) : (term285 m) = (term291 m).
Proof. exact (MK_COMB (@lem229300) (@lem229299 m)). Qed.
Lemma lem229302 : term286 = term292.
Proof. exact (fun_ext (fun m : nat => @lem229301 m)). Qed.
Lemma lem229303 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem229305 : term287 = term293.
Proof. exact (MK_COMB (@lem229303) (@lem229302)). Qed.
Lemma lem229306 (h1 : term246) : term293.
Proof. exact (EQ_MP (@lem229305) (@lem229258 h1)). Qed.
Lemma lem229307 (_4556 : nat) (h1 : term277) : term294 _4556.
Proof. exact (@lem229280 h1 _4556). Qed.
Lemma lem229308 (_4556 : nat) : (term294 _4556) = (term275 _4556).
Proof. exact (eq_refl (term294 _4556)). Qed.
Lemma lem229309 (_4556 : nat) (h1 : term277) : term275 _4556.
Proof. exact (EQ_MP (@lem229308 _4556) (@lem229307 _4556 h1)). Qed.
Lemma lem229310 (_4556 : nat) (_4557 : nat) (h1 : term277) : term295 _4556 _4557.
Proof. exact (@lem229309 _4556 h1 _4557). Qed.
Lemma lem229311 (_4557 : nat) (_4556 : nat) : (term295 _4556 _4557) = ((Nat.mul _4556 _4557) = (Nat.mul _4557 _4556)).
Proof. exact (eq_refl (term295 _4556 _4557)). Qed.
Lemma lem229313 (_4558 : nat) (h1 : term246) : term296 _4558.
Proof. exact (@lem229306 h1 _4558). Qed.
Lemma lem229314 (_4558 : nat) : (term296 _4558) = (term291 _4558).
Proof. exact (eq_refl (term296 _4558)). Qed.
Lemma lem229315 (_4558 : nat) (h1 : term246) : term291 _4558.
Proof. exact (EQ_MP (@lem229314 _4558) (@lem229313 _4558 h1)). Qed.
Lemma lem229316 (_4558 : nat) (_4559 : nat) (h1 : term246) : term297 _4558 _4559.
Proof. exact (@lem229315 _4558 h1 _4559). Qed.
Lemma lem229317 (_4558 : nat) (_4559 : nat) : (term297 _4558 _4559) = (term288 _4558 _4559).
Proof. exact (eq_refl (term297 _4558 _4559)). Qed.
Lemma lem229318 (_4558 : nat) (_4559 : nat) (h1 : term246) : term288 _4558 _4559.
Proof. exact (EQ_MP (@lem229317 _4558 _4559) (@lem229316 _4558 _4559 h1)). Qed.
Lemma lem229322 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem229324 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem229326 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem229334 (_4558 : nat) (_4559 : nat) (h1 : term246) : term298 _4558 _4559.
Proof. exact (proj1 (@lem229318 _4558 _4559 h1)). Qed.
Lemma lem229374 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : term299 _4558 _4559.
Proof. exact (h1). Qed.
Lemma lem229375 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : term300 _4558 _4559.
Proof. exact (@lem16684 (_4559 = (NUMERAL 0)) (_4558 = (term9 _4558 _4559)) h1). Qed.
Lemma lem229376 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : (term299 _4558 _4559) = (term300 _4558 _4559).
Proof. exact (prop_ext (fun h2 : term299 _4558 _4559 => @lem229375 _4558 _4559 h1) (fun h2 : term300 _4558 _4559 => @lem229374 _4558 _4559 h1)). Qed.
Lemma lem229377 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : term300 _4558 _4559.
Proof. exact (EQ_MP (@lem229376 _4558 _4559 h1) (@lem229374 _4558 _4559 h1)). Qed.
Lemma lem229378 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : term209 _4559.
Proof. exact (@lem16597 (_4559 = (NUMERAL 0)) (_4558 = (term9 _4558 _4559)) h1). Qed.
Lemma lem229379 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : (term299 _4558 _4559) = (term209 _4559).
Proof. exact (prop_ext (fun h2 : term299 _4558 _4559 => @lem229378 _4558 _4559 h1) (fun h2 : term209 _4559 => @lem229374 _4558 _4559 h1)). Qed.
Lemma lem229380 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : term209 _4559.
Proof. exact (EQ_MP (@lem229379 _4558 _4559 h1) (@lem229374 _4558 _4559 h1)). Qed.
Lemma lem229381 (_4558 : nat) (_4559 : nat) (h1 : term300 _4558 _4559) (h2 : term209 _4559) : term301 _4558 _4559.
Proof. exact (@lem16799 (_4558 = (term9 _4558 _4559)) (_4559 = (NUMERAL 0)) h1 h2). Qed.
Lemma lem229382 (_4558 : nat) (_4559 : nat) (h1 : term300 _4558 _4559) (h2 : term299 _4558 _4559) : (term209 _4559) = (term301 _4558 _4559).
Proof. exact (prop_ext (fun h3 : term209 _4559 => @lem229381 _4558 _4559 h1 h3) (fun h3 : term301 _4558 _4559 => @lem229380 _4558 _4559 h2)). Qed.
Lemma lem229383 (_4558 : nat) (_4559 : nat) (h1 : term300 _4558 _4559) (h2 : term299 _4558 _4559) : term301 _4558 _4559.
Proof. exact (EQ_MP (@lem229382 _4558 _4559 h1 h2) (@lem229380 _4558 _4559 h2)). Qed.
Lemma lem229384 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : (term300 _4558 _4559) = (term301 _4558 _4559).
Proof. exact (prop_ext (fun h2 : term300 _4558 _4559 => @lem229383 _4558 _4559 h2 h1) (fun h2 : term301 _4558 _4559 => @lem229377 _4558 _4559 h1)). Qed.
Lemma lem229385 (_4558 : nat) (_4559 : nat) (h1 : term299 _4558 _4559) : term301 _4558 _4559.
Proof. exact (EQ_MP (@lem229384 _4558 _4559 h1) (@lem229377 _4558 _4559 h1)). Qed.
Lemma lem229386 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : term301 _4558 _4559.
Proof. exact (h1). Qed.
Lemma lem229387 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : term209 _4559.
Proof. exact (@lem16684 (_4558 = (term9 _4558 _4559)) (_4559 = (NUMERAL 0)) h1). Qed.
Lemma lem229388 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : (term301 _4558 _4559) = (term209 _4559).
Proof. exact (prop_ext (fun h2 : term301 _4558 _4559 => @lem229387 _4558 _4559 h1) (fun h2 : term209 _4559 => @lem229386 _4558 _4559 h1)). Qed.
Lemma lem229389 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : term209 _4559.
Proof. exact (EQ_MP (@lem229388 _4558 _4559 h1) (@lem229386 _4558 _4559 h1)). Qed.
Lemma lem229390 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : term300 _4558 _4559.
Proof. exact (@lem16597 (_4558 = (term9 _4558 _4559)) (_4559 = (NUMERAL 0)) h1). Qed.
Lemma lem229391 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : (term301 _4558 _4559) = (term300 _4558 _4559).
Proof. exact (prop_ext (fun h2 : term301 _4558 _4559 => @lem229390 _4558 _4559 h1) (fun h2 : term300 _4558 _4559 => @lem229386 _4558 _4559 h1)). Qed.
Lemma lem229392 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : term300 _4558 _4559.
Proof. exact (EQ_MP (@lem229391 _4558 _4559 h1) (@lem229386 _4558 _4559 h1)). Qed.
Lemma lem229393 (_4558 : nat) (_4559 : nat) (h1 : term300 _4558 _4559) (h2 : term209 _4559) : term299 _4558 _4559.
Proof. exact (@lem16799 (_4559 = (NUMERAL 0)) (_4558 = (term9 _4558 _4559)) h2 h1). Qed.
Lemma lem229394 (_4558 : nat) (_4559 : nat) (h1 : term209 _4559) (h2 : term301 _4558 _4559) : (term300 _4558 _4559) = (term299 _4558 _4559).
Proof. exact (prop_ext (fun h3 : term300 _4558 _4559 => @lem229393 _4558 _4559 h3 h1) (fun h3 : term299 _4558 _4559 => @lem229392 _4558 _4559 h2)). Qed.
Lemma lem229395 (_4558 : nat) (_4559 : nat) (h1 : term209 _4559) (h2 : term301 _4558 _4559) : term299 _4558 _4559.
Proof. exact (EQ_MP (@lem229394 _4558 _4559 h1 h2) (@lem229392 _4558 _4559 h2)). Qed.
Lemma lem229396 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : (term209 _4559) = (term299 _4558 _4559).
Proof. exact (prop_ext (fun h2 : term209 _4559 => @lem229395 _4558 _4559 h2 h1) (fun h2 : term299 _4558 _4559 => @lem229389 _4558 _4559 h1)). Qed.
Lemma lem229397 (_4558 : nat) (_4559 : nat) (h1 : term301 _4558 _4559) : term299 _4558 _4559.
Proof. exact (EQ_MP (@lem229396 _4558 _4559 h1) (@lem229389 _4558 _4559 h1)). Qed.
Lemma lem229398 (_4558 : nat) (_4559 : nat) : term302 _4558 _4559.
Proof. exact (fun h0 : term301 _4558 _4559 => @lem229397 _4558 _4559 h0). Qed.
Lemma lem229399 (_4558 : nat) (_4559 : nat) : term303 _4558 _4559.
Proof. exact (fun h0 : term299 _4558 _4559 => @lem229385 _4558 _4559 h0). Qed.
Lemma lem229400 (_4558 : nat) (_4559 : nat) : term304 _4558 _4559.
Proof. exact (conj (@lem229399 _4558 _4559) (@lem229398 _4558 _4559)). Qed.
Lemma lem229401 (_4558 : nat) (_4559 : nat) : (term304 _4558 _4559) = ((term299 _4558 _4559) = (term301 _4558 _4559)).
Proof. exact (@lem32 (term299 _4558 _4559) (term301 _4558 _4559)). Qed.
Lemma lem229402 (_4558 : nat) (_4559 : nat) : (term299 _4558 _4559) = (term301 _4558 _4559).
Proof. exact (EQ_MP (@lem229401 _4558 _4559) (@lem229400 _4558 _4559)). Qed.
Lemma lem229403 (_4558 : nat) (_4559 : nat) (h1 : (term299 _4558 _4559) = (term301 _4558 _4559)) : (term298 _4558 _4559) = (term305 _4558 _4559).
Proof. exact (@lem16917 (term298 _4558 _4559) (term305 _4558 _4559) h1). Qed.
Lemma lem229404 (_4558 : nat) (_4559 : nat) : ((term299 _4558 _4559) = (term301 _4558 _4559)) = ((term298 _4558 _4559) = (term305 _4558 _4559)).
Proof. exact (prop_ext (fun h1 : (term299 _4558 _4559) = (term301 _4558 _4559) => @lem229403 _4558 _4559 h1) (fun h1 : (term298 _4558 _4559) = (term305 _4558 _4559) => @lem229402 _4558 _4559)). Qed.
Lemma lem229405 (_4558 : nat) (_4559 : nat) : (term298 _4558 _4559) = (term305 _4558 _4559).
Proof. exact (EQ_MP (@lem229404 _4558 _4559) (@lem229402 _4558 _4559)). Qed.
Lemma lem229406 (_4558 : nat) (_4559 : nat) (h1 : term246) : term305 _4558 _4559.
Proof. exact (EQ_MP (@lem229405 _4558 _4559) (@lem229334 _4558 _4559 h1)). Qed.
Lemma lem229408 (_4557 : nat) (_4556 : nat) (h1 : term277) : (Nat.mul _4556 _4557) = (Nat.mul _4557 _4556).
Proof. exact (EQ_MP (@lem229311 _4557 _4556) (@lem229310 _4556 _4557 h1)). Qed.
Lemma lem229418 (__1 : nat) (__0 : nat) (h1 : term246) : term305 __1 __0.
Proof. exact (@lem229406 __1 __0 h1). Qed.
Lemma lem229419 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : term301 __1 __0.
Proof. exact (h1). Qed.
Lemma lem229420 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : term209 __0.
Proof. exact (@lem16684 (__1 = (term9 __1 __0)) (__0 = (NUMERAL 0)) h1). Qed.
Lemma lem229421 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : (term301 __1 __0) = (term209 __0).
Proof. exact (prop_ext (fun h2 : term301 __1 __0 => @lem229420 __1 __0 h1) (fun h2 : term209 __0 => @lem229419 __1 __0 h1)). Qed.
Lemma lem229422 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : term209 __0.
Proof. exact (EQ_MP (@lem229421 __1 __0 h1) (@lem229419 __1 __0 h1)). Qed.
Lemma lem229423 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : term300 __1 __0.
Proof. exact (@lem16597 (__1 = (term9 __1 __0)) (__0 = (NUMERAL 0)) h1). Qed.
Lemma lem229424 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : (term301 __1 __0) = (term300 __1 __0).
Proof. exact (prop_ext (fun h2 : term301 __1 __0 => @lem229423 __1 __0 h1) (fun h2 : term300 __1 __0 => @lem229419 __1 __0 h1)). Qed.
Lemma lem229425 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : term300 __1 __0.
Proof. exact (EQ_MP (@lem229424 __1 __0 h1) (@lem229419 __1 __0 h1)). Qed.
Lemma lem229426 (__1 : nat) (__0 : nat) (h1 : term209 __0) (h2 : term300 __1 __0) : term299 __1 __0.
Proof. exact (@lem16799 (__0 = (NUMERAL 0)) (__1 = (term9 __1 __0)) h1 h2). Qed.
Lemma lem229427 (__1 : nat) (__0 : nat) (h1 : term209 __0) (h2 : term301 __1 __0) : (term300 __1 __0) = (term299 __1 __0).
Proof. exact (prop_ext (fun h3 : term300 __1 __0 => @lem229426 __1 __0 h1 h3) (fun h3 : term299 __1 __0 => @lem229425 __1 __0 h2)). Qed.
Lemma lem229428 (__1 : nat) (__0 : nat) (h1 : term209 __0) (h2 : term301 __1 __0) : term299 __1 __0.
Proof. exact (EQ_MP (@lem229427 __1 __0 h1 h2) (@lem229425 __1 __0 h2)). Qed.
Lemma lem229429 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : (term209 __0) = (term299 __1 __0).
Proof. exact (prop_ext (fun h2 : term209 __0 => @lem229428 __1 __0 h2 h1) (fun h2 : term299 __1 __0 => @lem229422 __1 __0 h1)). Qed.
Lemma lem229430 (__1 : nat) (__0 : nat) (h1 : term301 __1 __0) : term299 __1 __0.
Proof. exact (EQ_MP (@lem229429 __1 __0 h1) (@lem229422 __1 __0 h1)). Qed.
Lemma lem229431 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : term299 __1 __0.
Proof. exact (h1). Qed.
Lemma lem229432 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : term300 __1 __0.
Proof. exact (@lem16684 (__0 = (NUMERAL 0)) (__1 = (term9 __1 __0)) h1). Qed.
Lemma lem229433 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : (term299 __1 __0) = (term300 __1 __0).
Proof. exact (prop_ext (fun h2 : term299 __1 __0 => @lem229432 __1 __0 h1) (fun h2 : term300 __1 __0 => @lem229431 __1 __0 h1)). Qed.
Lemma lem229434 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : term300 __1 __0.
Proof. exact (EQ_MP (@lem229433 __1 __0 h1) (@lem229431 __1 __0 h1)). Qed.
Lemma lem229435 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : term209 __0.
Proof. exact (@lem16597 (__0 = (NUMERAL 0)) (__1 = (term9 __1 __0)) h1). Qed.
Lemma lem229436 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : (term299 __1 __0) = (term209 __0).
Proof. exact (prop_ext (fun h2 : term299 __1 __0 => @lem229435 __1 __0 h1) (fun h2 : term209 __0 => @lem229431 __1 __0 h1)). Qed.
Lemma lem229437 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : term209 __0.
Proof. exact (EQ_MP (@lem229436 __1 __0 h1) (@lem229431 __1 __0 h1)). Qed.
Lemma lem229438 (__1 : nat) (__0 : nat) (h1 : term209 __0) (h2 : term300 __1 __0) : term301 __1 __0.
Proof. exact (@lem16799 (__1 = (term9 __1 __0)) (__0 = (NUMERAL 0)) h2 h1). Qed.
Lemma lem229439 (__1 : nat) (__0 : nat) (h1 : term300 __1 __0) (h2 : term299 __1 __0) : (term209 __0) = (term301 __1 __0).
Proof. exact (prop_ext (fun h3 : term209 __0 => @lem229438 __1 __0 h3 h1) (fun h3 : term301 __1 __0 => @lem229437 __1 __0 h2)). Qed.
Lemma lem229440 (__1 : nat) (__0 : nat) (h1 : term300 __1 __0) (h2 : term299 __1 __0) : term301 __1 __0.
Proof. exact (EQ_MP (@lem229439 __1 __0 h1 h2) (@lem229437 __1 __0 h2)). Qed.
Lemma lem229441 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : (term300 __1 __0) = (term301 __1 __0).
Proof. exact (prop_ext (fun h2 : term300 __1 __0 => @lem229440 __1 __0 h2 h1) (fun h2 : term301 __1 __0 => @lem229434 __1 __0 h1)). Qed.
Lemma lem229442 (__1 : nat) (__0 : nat) (h1 : term299 __1 __0) : term301 __1 __0.
Proof. exact (EQ_MP (@lem229441 __1 __0 h1) (@lem229434 __1 __0 h1)). Qed.
Lemma lem229443 (__1 : nat) (__0 : nat) : term303 __1 __0.
Proof. exact (fun h0 : term299 __1 __0 => @lem229442 __1 __0 h0). Qed.
Lemma lem229444 (__1 : nat) (__0 : nat) : term302 __1 __0.
Proof. exact (fun h0 : term301 __1 __0 => @lem229430 __1 __0 h0). Qed.
Lemma lem229445 (__1 : nat) (__0 : nat) : term306 __1 __0.
Proof. exact (conj (@lem229444 __1 __0) (@lem229443 __1 __0)). Qed.
Lemma lem229446 (__1 : nat) (__0 : nat) : (term306 __1 __0) = ((term301 __1 __0) = (term299 __1 __0)).
Proof. exact (@lem32 (term301 __1 __0) (term299 __1 __0)). Qed.
Lemma lem229447 (__1 : nat) (__0 : nat) : (term301 __1 __0) = (term299 __1 __0).
Proof. exact (EQ_MP (@lem229446 __1 __0) (@lem229445 __1 __0)). Qed.
Lemma lem229448 (__1 : nat) (__0 : nat) (h1 : (term301 __1 __0) = (term299 __1 __0)) : (term305 __1 __0) = (term298 __1 __0).
Proof. exact (@lem16917 (term305 __1 __0) (term298 __1 __0) h1). Qed.
Lemma lem229449 (__1 : nat) (__0 : nat) : ((term301 __1 __0) = (term299 __1 __0)) = ((term305 __1 __0) = (term298 __1 __0)).
Proof. exact (prop_ext (fun h1 : (term301 __1 __0) = (term299 __1 __0) => @lem229448 __1 __0 h1) (fun h1 : (term305 __1 __0) = (term298 __1 __0) => @lem229447 __1 __0)). Qed.
Lemma lem229450 (__1 : nat) (__0 : nat) : (term305 __1 __0) = (term298 __1 __0).
Proof. exact (EQ_MP (@lem229449 __1 __0) (@lem229447 __1 __0)). Qed.
Lemma lem229456 {_12841 : Type'} (__x : _12841) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem229458 {_12843 : Type'} (__x : _12843) (h1 : __x = __x) : __x = __x.
Proof. exact (h1). Qed.
Lemma lem229460 {_12843 : Type'} (__x : _12843) (__y : _12843) (h1 : __x = __y) : __x = __y.
Proof. exact (h1). Qed.
Lemma lem229461 {_12843 : Type'} : (@eq _12843) = (@eq _12843).
Proof. exact (eq_refl (@eq _12843)). Qed.
Lemma lem229462 {_12843 : Type'} (__x : _12843) (__y : _12843) (h1 : __x = __y) : (@eq _12843 __x) = (@eq _12843 __y).
Proof. exact (MK_COMB (@lem229461 _12843) (@lem229460 _12843 __x __y h1)). Qed.
Lemma lem229463 {_12843 : Type'} (__x : _12843) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem229464 {_12843 : Type'} (__x : _12843) (__y : _12843) (h1 : __x = __y) : (__x = __x) = (__y = __x).
Proof. exact (MK_COMB (@lem229462 _12843 __x __y h1) (@lem229463 _12843 __x)). Qed.
Lemma lem229465 {_12843 : Type'} (__x : _12843) (__y : _12843) (h1 : __x = __x) (h2 : __x = __y) : __y = __x.
Proof. exact (EQ_MP (@lem229464 _12843 __x __y h2) (@lem229458 _12843 __x h1)). Qed.
Lemma lem229466 {_12843 : Type'} (__x : _12843) (__y : _12843) (h1 : __x = __y) : term307 _12843 __y __x.
Proof. exact (fun h0 : __x = __x => @lem229465 _12843 __x __y h0 h1). Qed.
Lemma lem229467 {_12843 : Type'} (__x : _12843) : term308 _12843 __x.
Proof. exact (@lem22518 (__x = __x)). Qed.
Lemma lem229468 {_12843 : Type'} (__x : _12843) : (term308 _12843 __x) = (term309 _12843 __x).
Proof. exact (eq_refl (term308 _12843 __x)). Qed.
Lemma lem229469 {_12843 : Type'} (__x : _12843) : term309 _12843 __x.
Proof. exact (EQ_MP (@lem229468 _12843 __x) (@lem229467 _12843 __x)). Qed.
Lemma lem229470 {_12843 : Type'} (__y : _12843) (__x : _12843) : term310 _12843 __y __x.
Proof. exact (@lem229469 _12843 __x (__y = __x)). Qed.
Lemma lem229471 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term310 _12843 __y __x) = ((term307 _12843 __y __x) = (term311 _12843 __y __x)).
Proof. exact (eq_refl (term310 _12843 __y __x)). Qed.
Lemma lem229474 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term307 _12843 __y __x) = (term311 _12843 __y __x).
Proof. exact (EQ_MP (@lem229471 _12843 __y __x) (@lem229470 _12843 __y __x)). Qed.
Lemma lem229475 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term307 _12843 __y __x) = (term311 _12843 __y __x).
Proof. exact (@lem229474 _12843 __y __x). Qed.
Lemma lem229476 {_12843 : Type'} (__x : _12843) (__y : _12843) (h1 : __x = __y) : term311 _12843 __y __x.
Proof. exact (EQ_MP (@lem229475 _12843 __y __x) (@lem229466 _12843 __x __y h1)). Qed.
Lemma lem229477 {_12843 : Type'} (__y : _12843) (__x : _12843) : term312 _12843 __y __x.
Proof. exact (fun h0 : __x = __y => @lem229476 _12843 __x __y h0). Qed.
Lemma lem229478 {_12843 : Type'} (__x : _12843) (__y : _12843) : term313 _12843 __x __y.
Proof. exact (@lem22518 (__x = __y)). Qed.
Lemma lem229479 {_12843 : Type'} (__x : _12843) (__y : _12843) : (term313 _12843 __x __y) = (term314 _12843 __x __y).
Proof. exact (eq_refl (term313 _12843 __x __y)). Qed.
Lemma lem229480 {_12843 : Type'} (__x : _12843) (__y : _12843) : term314 _12843 __x __y.
Proof. exact (EQ_MP (@lem229479 _12843 __x __y) (@lem229478 _12843 __x __y)). Qed.
Lemma lem229481 {_12843 : Type'} (__y : _12843) (__x : _12843) : term315 _12843 __y __x.
Proof. exact (@lem229480 _12843 __x __y (term311 _12843 __y __x)). Qed.
Lemma lem229482 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term315 _12843 __y __x) = ((term312 _12843 __y __x) = (term316 _12843 __y __x)).
Proof. exact (eq_refl (term315 _12843 __y __x)). Qed.
Lemma lem229485 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term312 _12843 __y __x) = (term316 _12843 __y __x).
Proof. exact (EQ_MP (@lem229482 _12843 __y __x) (@lem229481 _12843 __y __x)). Qed.
Lemma lem229486 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term312 _12843 __y __x) = (term316 _12843 __y __x).
Proof. exact (@lem229485 _12843 __y __x). Qed.
Lemma lem229487 {_12843 : Type'} (__y : _12843) (__x : _12843) : term316 _12843 __y __x.
Proof. exact (EQ_MP (@lem229486 _12843 __y __x) (@lem229477 _12843 __y __x)). Qed.
Lemma lem229488 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term317 _12843 __y __x.
Proof. exact (h1). Qed.
Lemma lem229489 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term318 _12843 __y __x.
Proof. exact (@lem16684 (term319 _12843 __x __y) (term311 _12843 __y __x) h1). Qed.
Lemma lem229490 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : (term317 _12843 __y __x) = (term318 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term317 _12843 __y __x => @lem229489 _12843 __y __x h1) (fun h2 : term318 _12843 __y __x => @lem229488 _12843 __y __x h1)). Qed.
Lemma lem229491 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term318 _12843 __y __x.
Proof. exact (EQ_MP (@lem229490 _12843 __y __x h1) (@lem229488 _12843 __y __x h1)). Qed.
Lemma lem229492 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term320 _12843 __x __y.
Proof. exact (@lem16597 (term319 _12843 __x __y) (term311 _12843 __y __x) h1). Qed.
Lemma lem229493 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : (term317 _12843 __y __x) = (term320 _12843 __x __y).
Proof. exact (prop_ext (fun h2 : term317 _12843 __y __x => @lem229492 _12843 __y __x h1) (fun h2 : term320 _12843 __x __y => @lem229488 _12843 __y __x h1)). Qed.
Lemma lem229494 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term320 _12843 __x __y.
Proof. exact (EQ_MP (@lem229493 _12843 __y __x h1) (@lem229488 _12843 __y __x h1)). Qed.
Lemma lem229495 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term318 _12843 __y __x) : term319 _12843 __y __x.
Proof. exact (@lem16684 (term321 _12843 __x) (__y = __x) h1). Qed.
Lemma lem229496 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : (term318 _12843 __y __x) = (term319 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term318 _12843 __y __x => @lem229495 _12843 __y __x h2) (fun h2 : term319 _12843 __y __x => @lem229491 _12843 __y __x h1)). Qed.
Lemma lem229497 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term319 _12843 __y __x.
Proof. exact (EQ_MP (@lem229496 _12843 __y __x h1) (@lem229491 _12843 __y __x h1)). Qed.
Lemma lem229498 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term318 _12843 __y __x) : term322 _12843 __x.
Proof. exact (@lem16597 (term321 _12843 __x) (__y = __x) h1). Qed.
Lemma lem229499 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : (term318 _12843 __y __x) = (term322 _12843 __x).
Proof. exact (prop_ext (fun h2 : term318 _12843 __y __x => @lem229498 _12843 __y __x h2) (fun h2 : term322 _12843 __x => @lem229491 _12843 __y __x h1)). Qed.
Lemma lem229500 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term322 _12843 __x.
Proof. exact (EQ_MP (@lem229499 _12843 __y __x h1) (@lem229491 _12843 __y __x h1)). Qed.
Lemma lem229501 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term320 _12843 __x __y) (h2 : term319 _12843 __y __x) : term323 _12843 __y __x.
Proof. exact (@lem16799 (term319 _12843 __x __y) (__y = __x) h1 h2). Qed.
Lemma lem229502 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term320 _12843 __x __y) (h2 : term317 _12843 __y __x) : (term319 _12843 __y __x) = (term323 _12843 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _12843 __y __x => @lem229501 _12843 __y __x h1 h3) (fun h3 : term323 _12843 __y __x => @lem229497 _12843 __y __x h2)). Qed.
Lemma lem229503 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term320 _12843 __x __y) (h2 : term317 _12843 __y __x) : term323 _12843 __y __x.
Proof. exact (EQ_MP (@lem229502 _12843 __y __x h1 h2) (@lem229497 _12843 __y __x h2)). Qed.
Lemma lem229504 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : (term320 _12843 __x __y) = (term323 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _12843 __x __y => @lem229503 _12843 __y __x h2 h1) (fun h2 : term323 _12843 __y __x => @lem229494 _12843 __y __x h1)). Qed.
Lemma lem229505 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term323 _12843 __y __x.
Proof. exact (EQ_MP (@lem229504 _12843 __y __x h1) (@lem229494 _12843 __y __x h1)). Qed.
Lemma lem229506 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term322 _12843 __x) (h2 : term323 _12843 __y __x) : term324 _12843 __y __x.
Proof. exact (@lem16799 (term321 _12843 __x) (term325 _12843 __y __x) h1 h2). Qed.
Lemma lem229507 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term322 _12843 __x) (h2 : term317 _12843 __y __x) : (term323 _12843 __y __x) = (term324 _12843 __y __x).
Proof. exact (prop_ext (fun h3 : term323 _12843 __y __x => @lem229506 _12843 __y __x h1 h3) (fun h3 : term324 _12843 __y __x => @lem229505 _12843 __y __x h2)). Qed.
Lemma lem229508 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term322 _12843 __x) (h2 : term317 _12843 __y __x) : term324 _12843 __y __x.
Proof. exact (EQ_MP (@lem229507 _12843 __y __x h1 h2) (@lem229505 _12843 __y __x h2)). Qed.
Lemma lem229509 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : (term322 _12843 __x) = (term324 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _12843 __x => @lem229508 _12843 __y __x h2 h1) (fun h2 : term324 _12843 __y __x => @lem229500 _12843 __y __x h1)). Qed.
Lemma lem229510 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term317 _12843 __y __x) : term324 _12843 __y __x.
Proof. exact (EQ_MP (@lem229509 _12843 __y __x h1) (@lem229500 _12843 __y __x h1)). Qed.
Lemma lem229511 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term324 _12843 __y __x.
Proof. exact (h1). Qed.
Lemma lem229512 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term323 _12843 __y __x.
Proof. exact (@lem16684 (term321 _12843 __x) (term325 _12843 __y __x) h1). Qed.
Lemma lem229513 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : (term324 _12843 __y __x) = (term323 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term324 _12843 __y __x => @lem229512 _12843 __y __x h1) (fun h2 : term323 _12843 __y __x => @lem229511 _12843 __y __x h1)). Qed.
Lemma lem229514 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term323 _12843 __y __x.
Proof. exact (EQ_MP (@lem229513 _12843 __y __x h1) (@lem229511 _12843 __y __x h1)). Qed.
Lemma lem229515 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term322 _12843 __x.
Proof. exact (@lem16597 (term321 _12843 __x) (term325 _12843 __y __x) h1). Qed.
Lemma lem229516 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : (term324 _12843 __y __x) = (term322 _12843 __x).
Proof. exact (prop_ext (fun h2 : term324 _12843 __y __x => @lem229515 _12843 __y __x h1) (fun h2 : term322 _12843 __x => @lem229511 _12843 __y __x h1)). Qed.
Lemma lem229517 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term322 _12843 __x.
Proof. exact (EQ_MP (@lem229516 _12843 __y __x h1) (@lem229511 _12843 __y __x h1)). Qed.
Lemma lem229518 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term323 _12843 __y __x) : term319 _12843 __y __x.
Proof. exact (@lem16684 (term319 _12843 __x __y) (__y = __x) h1). Qed.
Lemma lem229519 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : (term323 _12843 __y __x) = (term319 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term323 _12843 __y __x => @lem229518 _12843 __y __x h2) (fun h2 : term319 _12843 __y __x => @lem229514 _12843 __y __x h1)). Qed.
Lemma lem229520 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term319 _12843 __y __x.
Proof. exact (EQ_MP (@lem229519 _12843 __y __x h1) (@lem229514 _12843 __y __x h1)). Qed.
Lemma lem229521 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term323 _12843 __y __x) : term320 _12843 __x __y.
Proof. exact (@lem16597 (term319 _12843 __x __y) (__y = __x) h1). Qed.
Lemma lem229522 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : (term323 _12843 __y __x) = (term320 _12843 __x __y).
Proof. exact (prop_ext (fun h2 : term323 _12843 __y __x => @lem229521 _12843 __y __x h2) (fun h2 : term320 _12843 __x __y => @lem229514 _12843 __y __x h1)). Qed.
Lemma lem229523 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term320 _12843 __x __y.
Proof. exact (EQ_MP (@lem229522 _12843 __y __x h1) (@lem229514 _12843 __y __x h1)). Qed.
Lemma lem229524 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term322 _12843 __x) (h2 : term319 _12843 __y __x) : term318 _12843 __y __x.
Proof. exact (@lem16799 (term321 _12843 __x) (__y = __x) h1 h2). Qed.
Lemma lem229525 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term322 _12843 __x) (h2 : term324 _12843 __y __x) : (term319 _12843 __y __x) = (term318 _12843 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _12843 __y __x => @lem229524 _12843 __y __x h1 h3) (fun h3 : term318 _12843 __y __x => @lem229520 _12843 __y __x h2)). Qed.
Lemma lem229526 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term322 _12843 __x) (h2 : term324 _12843 __y __x) : term318 _12843 __y __x.
Proof. exact (EQ_MP (@lem229525 _12843 __y __x h1 h2) (@lem229520 _12843 __y __x h2)). Qed.
Lemma lem229527 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : (term322 _12843 __x) = (term318 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _12843 __x => @lem229526 _12843 __y __x h2 h1) (fun h2 : term318 _12843 __y __x => @lem229517 _12843 __y __x h1)). Qed.
Lemma lem229528 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term318 _12843 __y __x.
Proof. exact (EQ_MP (@lem229527 _12843 __y __x h1) (@lem229517 _12843 __y __x h1)). Qed.
Lemma lem229529 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term320 _12843 __x __y) (h2 : term318 _12843 __y __x) : term317 _12843 __y __x.
Proof. exact (@lem16799 (term319 _12843 __x __y) (term311 _12843 __y __x) h1 h2). Qed.
Lemma lem229530 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term320 _12843 __x __y) (h2 : term324 _12843 __y __x) : (term318 _12843 __y __x) = (term317 _12843 __y __x).
Proof. exact (prop_ext (fun h3 : term318 _12843 __y __x => @lem229529 _12843 __y __x h1 h3) (fun h3 : term317 _12843 __y __x => @lem229528 _12843 __y __x h2)). Qed.
Lemma lem229531 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term320 _12843 __x __y) (h2 : term324 _12843 __y __x) : term317 _12843 __y __x.
Proof. exact (EQ_MP (@lem229530 _12843 __y __x h1 h2) (@lem229528 _12843 __y __x h2)). Qed.
Lemma lem229532 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : (term320 _12843 __x __y) = (term317 _12843 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _12843 __x __y => @lem229531 _12843 __y __x h2 h1) (fun h2 : term317 _12843 __y __x => @lem229523 _12843 __y __x h1)). Qed.
Lemma lem229533 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : term324 _12843 __y __x) : term317 _12843 __y __x.
Proof. exact (EQ_MP (@lem229532 _12843 __y __x h1) (@lem229523 _12843 __y __x h1)). Qed.
Lemma lem229534 {_12843 : Type'} (__y : _12843) (__x : _12843) : term326 _12843 __y __x.
Proof. exact (fun h0 : term324 _12843 __y __x => @lem229533 _12843 __y __x h0). Qed.
Lemma lem229535 {_12843 : Type'} (__y : _12843) (__x : _12843) : term327 _12843 __y __x.
Proof. exact (fun h0 : term317 _12843 __y __x => @lem229510 _12843 __y __x h0). Qed.
Lemma lem229536 {_12843 : Type'} (__y : _12843) (__x : _12843) : term328 _12843 __y __x.
Proof. exact (conj (@lem229535 _12843 __y __x) (@lem229534 _12843 __y __x)). Qed.
Lemma lem229537 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term328 _12843 __y __x) = ((term317 _12843 __y __x) = (term324 _12843 __y __x)).
Proof. exact (@lem32 (term317 _12843 __y __x) (term324 _12843 __y __x)). Qed.
Lemma lem229538 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term317 _12843 __y __x) = (term324 _12843 __y __x).
Proof. exact (EQ_MP (@lem229537 _12843 __y __x) (@lem229536 _12843 __y __x)). Qed.
Lemma lem229539 {_12843 : Type'} (__y : _12843) (__x : _12843) (h1 : (term317 _12843 __y __x) = (term324 _12843 __y __x)) : (term316 _12843 __y __x) = (term329 _12843 __y __x).
Proof. exact (@lem16917 (term316 _12843 __y __x) (term329 _12843 __y __x) h1). Qed.
Lemma lem229540 {_12843 : Type'} (__y : _12843) (__x : _12843) : ((term317 _12843 __y __x) = (term324 _12843 __y __x)) = ((term316 _12843 __y __x) = (term329 _12843 __y __x)).
Proof. exact (prop_ext (fun h1 : (term317 _12843 __y __x) = (term324 _12843 __y __x) => @lem229539 _12843 __y __x h1) (fun h1 : (term316 _12843 __y __x) = (term329 _12843 __y __x) => @lem229538 _12843 __y __x)). Qed.
Lemma lem229541 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term316 _12843 __y __x) = (term329 _12843 __y __x).
Proof. exact (EQ_MP (@lem229540 _12843 __y __x) (@lem229538 _12843 __y __x)). Qed.
Lemma lem229542 {_12843 : Type'} (__y : _12843) (__x : _12843) : term329 _12843 __y __x.
Proof. exact (EQ_MP (@lem229541 _12843 __y __x) (@lem229487 _12843 __y __x)). Qed.
Lemma lem229543 {_12843 : Type'} (__y : _12843) (__x : _12843) : term329 _12843 __y __x.
Proof. exact (@lem229542 _12843 __y __x). Qed.
Lemma lem229544 {_12843 : Type'} (__x : _12843) : __x = __x.
Proof. exact (@lem229456 _12843 __x). Qed.
Lemma lem229547 {_12843 : Type'} (__x : _12843) : (__x = __x) = (__x = __x).
Proof. exact (eq_refl (__x = __x)). Qed.
Lemma lem229548 {_12843 : Type'} (__x : _12843) : (__x = __x) = (__x = __x).
Proof. exact (@lem229547 _12843 __x). Qed.
Lemma lem229549 {_12843 : Type'} (__x : _12843) : __x = __x.
Proof. exact (EQ_MP (@lem229548 _12843 __x) (@lem229544 _12843 __x)). Qed.
Lemma lem229552 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term329 _12843 __y __x) = (term329 _12843 __y __x).
Proof. exact (eq_refl (term329 _12843 __y __x)). Qed.
Lemma lem229553 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term329 _12843 __y __x) = (term329 _12843 __y __x).
Proof. exact (@lem229552 _12843 __y __x). Qed.
Lemma lem229554 {_12843 : Type'} (__y : _12843) (__x : _12843) : term329 _12843 __y __x.
Proof. exact (EQ_MP (@lem229553 _12843 __y __x) (@lem229543 _12843 __y __x)). Qed.
Lemma lem229555 {_12843 : Type'} (__x : _12843) : term330 _12843 __x.
Proof. exact (@lem22025 (__x = __x)). Qed.
Lemma lem229556 {_12843 : Type'} (__x : _12843) : (term330 _12843 __x) = (term331 _12843 __x).
Proof. exact (eq_refl (term330 _12843 __x)). Qed.
Lemma lem229557 {_12843 : Type'} (__x : _12843) : term331 _12843 __x.
Proof. exact (EQ_MP (@lem229556 _12843 __x) (@lem229555 _12843 __x)). Qed.
Lemma lem229558 {_12843 : Type'} (__y : _12843) (__x : _12843) : term332 _12843 __y __x.
Proof. exact (@lem229557 _12843 __x (term325 _12843 __y __x)). Qed.
Lemma lem229559 {_12843 : Type'} (__y : _12843) (__x : _12843) : (term332 _12843 __y __x) = (term333 _12843 __y __x).
Proof. exact (eq_refl (term332 _12843 __y __x)). Qed.
Lemma lem229560 {_12843 : Type'} (__y : _12843) (__x : _12843) : term333 _12843 __y __x.
Proof. exact (EQ_MP (@lem229559 _12843 __y __x) (@lem229558 _12843 __y __x)). Qed.
Lemma lem229561 {_12843 : Type'} (__y : _12843) (__x : _12843) : term334 _12843 __y __x.
Proof. exact (@lem229560 _12843 __y __x (@lem229549 _12843 __x)). Qed.
Lemma lem229564 {_12843 : Type'} (__y : _12843) (__x : _12843) : term325 _12843 __y __x.
Proof. exact (@lem229561 _12843 __y __x (@lem229554 _12843 __y __x)). Qed.
Lemma lem229565 (__y : nat) (__x : nat) : term335 __y __x.
Proof. exact (@lem229564 nat __y __x). Qed.
Lemma lem229572 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem229576 (p : nat) : term336 p.
Proof. exact (@lem229565 (NUMERAL 0) p). Qed.
Lemma lem229577 (p : nat) : term337 p.
Proof. exact (@lem22025 (p = (NUMERAL 0))). Qed.
Lemma lem229578 (p : nat) : (term337 p) = (term338 p).
Proof. exact (eq_refl (term337 p)). Qed.
Lemma lem229579 (p : nat) : term338 p.
Proof. exact (EQ_MP (@lem229578 p) (@lem229577 p)). Qed.
Lemma lem229580 (p : nat) : term339 p.
Proof. exact (@lem229579 p ((NUMERAL 0) = p)). Qed.
Lemma lem229581 (p : nat) : (term339 p) = (term340 p).
Proof. exact (eq_refl (term339 p)). Qed.
Lemma lem229582 (p : nat) : term340 p.
Proof. exact (EQ_MP (@lem229581 p) (@lem229580 p)). Qed.
Lemma lem229583 (p : nat) (h1 : p = (NUMERAL 0)) : term341 p.
Proof. exact (@lem229582 p (@lem229572 p h1)). Qed.
Lemma lem229590 (__0 : nat) (p : nat) (h1 : term87 __0 p) : term87 __0 p.
Proof. exact (h1). Qed.
Lemma lem229592 (__0 : nat) (h1 : __0 = (NUMERAL 0)) : __0 = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem229593 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem229594 (__0 : nat) (h1 : __0 = (NUMERAL 0)) : (@eq nat __0) = term342.
Proof. exact (MK_COMB (@lem229593) (@lem229592 __0 h1)). Qed.
Lemma lem229595 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem229596 (p : nat) (__0 : nat) (h1 : __0 = (NUMERAL 0)) : (__0 = p) = ((NUMERAL 0) = p).
Proof. exact (MK_COMB (@lem229594 __0 h1) (@lem229595 p)). Qed.
Lemma lem229597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem229598 (p : nat) (__0 : nat) (h1 : __0 = (NUMERAL 0)) : (term87 __0 p) = (term343 p).
Proof. exact (MK_COMB (@lem229597) (@lem229596 p __0 h1)). Qed.
Lemma lem229599 (p : nat) (__0 : nat) (h1 : term87 __0 p) (h2 : __0 = (NUMERAL 0)) : term343 p.
Proof. exact (EQ_MP (@lem229598 p __0 h2) (@lem229590 __0 p h1)). Qed.
Lemma lem229600 (p : nat) (__0 : nat) (h1 : __0 = (NUMERAL 0)) : term344 __0 p.
Proof. exact (fun h0 : term87 __0 p => @lem229599 p __0 h0 h1). Qed.
Lemma lem229601 (__0 : nat) (p : nat) : term345 __0 p.
Proof. exact (@lem22403 (__0 = p)). Qed.
Lemma lem229602 (__0 : nat) (p : nat) : (term345 __0 p) = (term346 __0 p).
Proof. exact (eq_refl (term345 __0 p)). Qed.
Lemma lem229603 (__0 : nat) (p : nat) : term346 __0 p.
Proof. exact (EQ_MP (@lem229602 __0 p) (@lem229601 __0 p)). Qed.
Lemma lem229604 (__0 : nat) (p : nat) : term347 __0 p.
Proof. exact (@lem229603 __0 p (term343 p)). Qed.
Lemma lem229605 (__0 : nat) (p : nat) : (term347 __0 p) = ((term344 __0 p) = (term348 __0 p)).
Proof. exact (eq_refl (term347 __0 p)). Qed.
Lemma lem229608 (__0 : nat) (p : nat) : (term344 __0 p) = (term348 __0 p).
Proof. exact (EQ_MP (@lem229605 __0 p) (@lem229604 __0 p)). Qed.
Lemma lem229609 (p : nat) (__0 : nat) (h1 : __0 = (NUMERAL 0)) : term348 __0 p.
Proof. exact (EQ_MP (@lem229608 __0 p) (@lem229600 p __0 h1)). Qed.
Lemma lem229610 (__0 : nat) (p : nat) : term349 __0 p.
Proof. exact (fun h0 : __0 = (NUMERAL 0) => @lem229609 p __0 h0). Qed.
Lemma lem229611 (__0 : nat) : term350 __0.
Proof. exact (@lem22518 (__0 = (NUMERAL 0))). Qed.
Lemma lem229612 (__0 : nat) : (term350 __0) = (term351 __0).
Proof. exact (eq_refl (term350 __0)). Qed.
Lemma lem229613 (__0 : nat) : term351 __0.
Proof. exact (EQ_MP (@lem229612 __0) (@lem229611 __0)). Qed.
Lemma lem229614 (__0 : nat) (p : nat) : term352 __0 p.
Proof. exact (@lem229613 __0 (term348 __0 p)). Qed.
Lemma lem229615 (__0 : nat) (p : nat) : (term352 __0 p) = ((term349 __0 p) = (term353 __0 p)).
Proof. exact (eq_refl (term352 __0 p)). Qed.
Lemma lem229618 (__0 : nat) (p : nat) : (term349 __0 p) = (term353 __0 p).
Proof. exact (EQ_MP (@lem229615 __0 p) (@lem229614 __0 p)). Qed.
Lemma lem229619 (__0 : nat) (p : nat) : term353 __0 p.
Proof. exact (EQ_MP (@lem229618 __0 p) (@lem229610 __0 p)). Qed.
Lemma lem229620 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term354 __0 p.
Proof. exact (h1). Qed.
Lemma lem229621 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term355 __0 p.
Proof. exact (@lem16684 (term209 __0) (term348 __0 p) h1). Qed.
Lemma lem229622 (__0 : nat) (p : nat) (h1 : term354 __0 p) : (term354 __0 p) = (term355 __0 p).
Proof. exact (prop_ext (fun h2 : term354 __0 p => @lem229621 __0 p h1) (fun h2 : term355 __0 p => @lem229620 __0 p h1)). Qed.
Lemma lem229623 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term355 __0 p.
Proof. exact (EQ_MP (@lem229622 __0 p h1) (@lem229620 __0 p h1)). Qed.
Lemma lem229624 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term278 __0.
Proof. exact (@lem16597 (term209 __0) (term348 __0 p) h1). Qed.
Lemma lem229625 (__0 : nat) (p : nat) (h1 : term354 __0 p) : (term354 __0 p) = (term278 __0).
Proof. exact (prop_ext (fun h2 : term354 __0 p => @lem229624 __0 p h1) (fun h2 : term278 __0 => @lem229620 __0 p h1)). Qed.
Lemma lem229626 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term278 __0.
Proof. exact (EQ_MP (@lem229625 __0 p h1) (@lem229620 __0 p h1)). Qed.
Lemma lem229627 (__0 : nat) (p : nat) (h1 : term355 __0 p) : term356 p.
Proof. exact (@lem16684 (__0 = p) (term343 p) h1). Qed.
Lemma lem229628 (__0 : nat) (p : nat) (h1 : term354 __0 p) : (term355 __0 p) = (term356 p).
Proof. exact (prop_ext (fun h2 : term355 __0 p => @lem229627 __0 p h2) (fun h2 : term356 p => @lem229623 __0 p h1)). Qed.
Lemma lem229629 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term356 p.
Proof. exact (EQ_MP (@lem229628 __0 p h1) (@lem229623 __0 p h1)). Qed.
Lemma lem229630 (__0 : nat) (p : nat) (h1 : term355 __0 p) : term87 __0 p.
Proof. exact (@lem16597 (__0 = p) (term343 p) h1). Qed.
Lemma lem229631 (__0 : nat) (p : nat) (h1 : term354 __0 p) : (term355 __0 p) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term355 __0 p => @lem229630 __0 p h2) (fun h2 : term87 __0 p => @lem229623 __0 p h1)). Qed.
Lemma lem229632 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term87 __0 p.
Proof. exact (EQ_MP (@lem229631 __0 p h1) (@lem229623 __0 p h1)). Qed.
Lemma lem229633 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term87 __0 p) : term357 __0 p.
Proof. exact (@lem16799 (term343 p) (__0 = p) h1 h2). Qed.
Lemma lem229634 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term354 __0 p) : (term87 __0 p) = (term357 __0 p).
Proof. exact (prop_ext (fun h3 : term87 __0 p => @lem229633 __0 p h1 h3) (fun h3 : term357 __0 p => @lem229632 __0 p h2)). Qed.
Lemma lem229635 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term354 __0 p) : term357 __0 p.
Proof. exact (EQ_MP (@lem229634 __0 p h1 h2) (@lem229632 __0 p h2)). Qed.
Lemma lem229636 (__0 : nat) (p : nat) (h1 : term354 __0 p) : (term356 p) = (term357 __0 p).
Proof. exact (prop_ext (fun h2 : term356 p => @lem229635 __0 p h2 h1) (fun h2 : term357 __0 p => @lem229629 __0 p h1)). Qed.
Lemma lem229637 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term357 __0 p.
Proof. exact (EQ_MP (@lem229636 __0 p h1) (@lem229629 __0 p h1)). Qed.
Lemma lem229638 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term357 __0 p) : term358 __0 p.
Proof. exact (@lem16799 (term209 __0) (term359 __0 p) h1 h2). Qed.
Lemma lem229639 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term354 __0 p) : (term357 __0 p) = (term358 __0 p).
Proof. exact (prop_ext (fun h3 : term357 __0 p => @lem229638 __0 p h1 h3) (fun h3 : term358 __0 p => @lem229637 __0 p h2)). Qed.
Lemma lem229640 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term354 __0 p) : term358 __0 p.
Proof. exact (EQ_MP (@lem229639 __0 p h1 h2) (@lem229637 __0 p h2)). Qed.
Lemma lem229641 (__0 : nat) (p : nat) (h1 : term354 __0 p) : (term278 __0) = (term358 __0 p).
Proof. exact (prop_ext (fun h2 : term278 __0 => @lem229640 __0 p h2 h1) (fun h2 : term358 __0 p => @lem229626 __0 p h1)). Qed.
Lemma lem229642 (__0 : nat) (p : nat) (h1 : term354 __0 p) : term358 __0 p.
Proof. exact (EQ_MP (@lem229641 __0 p h1) (@lem229626 __0 p h1)). Qed.
Lemma lem229643 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term358 __0 p.
Proof. exact (h1). Qed.
Lemma lem229644 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term357 __0 p.
Proof. exact (@lem16684 (term209 __0) (term359 __0 p) h1). Qed.
Lemma lem229645 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term358 __0 p) = (term357 __0 p).
Proof. exact (prop_ext (fun h2 : term358 __0 p => @lem229644 __0 p h1) (fun h2 : term357 __0 p => @lem229643 __0 p h1)). Qed.
Lemma lem229646 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term357 __0 p.
Proof. exact (EQ_MP (@lem229645 __0 p h1) (@lem229643 __0 p h1)). Qed.
Lemma lem229647 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term278 __0.
Proof. exact (@lem16597 (term209 __0) (term359 __0 p) h1). Qed.
Lemma lem229648 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term358 __0 p) = (term278 __0).
Proof. exact (prop_ext (fun h2 : term358 __0 p => @lem229647 __0 p h1) (fun h2 : term278 __0 => @lem229643 __0 p h1)). Qed.
Lemma lem229649 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term278 __0.
Proof. exact (EQ_MP (@lem229648 __0 p h1) (@lem229643 __0 p h1)). Qed.
Lemma lem229650 (__0 : nat) (p : nat) (h1 : term357 __0 p) : term87 __0 p.
Proof. exact (@lem16684 (term343 p) (__0 = p) h1). Qed.
Lemma lem229651 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term357 __0 p) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term357 __0 p => @lem229650 __0 p h2) (fun h2 : term87 __0 p => @lem229646 __0 p h1)). Qed.
Lemma lem229652 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term87 __0 p.
Proof. exact (EQ_MP (@lem229651 __0 p h1) (@lem229646 __0 p h1)). Qed.
Lemma lem229653 (__0 : nat) (p : nat) (h1 : term357 __0 p) : term356 p.
Proof. exact (@lem16597 (term343 p) (__0 = p) h1). Qed.
Lemma lem229654 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term357 __0 p) = (term356 p).
Proof. exact (prop_ext (fun h2 : term357 __0 p => @lem229653 __0 p h2) (fun h2 : term356 p => @lem229646 __0 p h1)). Qed.
Lemma lem229655 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term356 p.
Proof. exact (EQ_MP (@lem229654 __0 p h1) (@lem229646 __0 p h1)). Qed.
Lemma lem229656 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term87 __0 p) : term355 __0 p.
Proof. exact (@lem16799 (__0 = p) (term343 p) h2 h1). Qed.
Lemma lem229657 (__0 : nat) (p : nat) (h1 : term87 __0 p) (h2 : term358 __0 p) : (term356 p) = (term355 __0 p).
Proof. exact (prop_ext (fun h3 : term356 p => @lem229656 __0 p h3 h1) (fun h3 : term355 __0 p => @lem229655 __0 p h2)). Qed.
Lemma lem229658 (__0 : nat) (p : nat) (h1 : term87 __0 p) (h2 : term358 __0 p) : term355 __0 p.
Proof. exact (EQ_MP (@lem229657 __0 p h1 h2) (@lem229655 __0 p h2)). Qed.
Lemma lem229659 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term87 __0 p) = (term355 __0 p).
Proof. exact (prop_ext (fun h2 : term87 __0 p => @lem229658 __0 p h2 h1) (fun h2 : term355 __0 p => @lem229652 __0 p h1)). Qed.
Lemma lem229660 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term355 __0 p.
Proof. exact (EQ_MP (@lem229659 __0 p h1) (@lem229652 __0 p h1)). Qed.
Lemma lem229661 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term355 __0 p) : term354 __0 p.
Proof. exact (@lem16799 (term209 __0) (term348 __0 p) h1 h2). Qed.
Lemma lem229662 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term358 __0 p) : (term355 __0 p) = (term354 __0 p).
Proof. exact (prop_ext (fun h3 : term355 __0 p => @lem229661 __0 p h1 h3) (fun h3 : term354 __0 p => @lem229660 __0 p h2)). Qed.
Lemma lem229663 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term358 __0 p) : term354 __0 p.
Proof. exact (EQ_MP (@lem229662 __0 p h1 h2) (@lem229660 __0 p h2)). Qed.
Lemma lem229664 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term278 __0) = (term354 __0 p).
Proof. exact (prop_ext (fun h2 : term278 __0 => @lem229663 __0 p h2 h1) (fun h2 : term354 __0 p => @lem229649 __0 p h1)). Qed.
Lemma lem229665 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term354 __0 p.
Proof. exact (EQ_MP (@lem229664 __0 p h1) (@lem229649 __0 p h1)). Qed.
Lemma lem229666 (__0 : nat) (p : nat) : term360 __0 p.
Proof. exact (fun h0 : term358 __0 p => @lem229665 __0 p h0). Qed.
Lemma lem229667 (__0 : nat) (p : nat) : term361 __0 p.
Proof. exact (fun h0 : term354 __0 p => @lem229642 __0 p h0). Qed.
Lemma lem229668 (__0 : nat) (p : nat) : term362 __0 p.
Proof. exact (conj (@lem229667 __0 p) (@lem229666 __0 p)). Qed.
Lemma lem229669 (__0 : nat) (p : nat) : (term362 __0 p) = ((term354 __0 p) = (term358 __0 p)).
Proof. exact (@lem32 (term354 __0 p) (term358 __0 p)). Qed.
Lemma lem229670 (__0 : nat) (p : nat) : (term354 __0 p) = (term358 __0 p).
Proof. exact (EQ_MP (@lem229669 __0 p) (@lem229668 __0 p)). Qed.
Lemma lem229671 (__0 : nat) (p : nat) (h1 : (term354 __0 p) = (term358 __0 p)) : (term353 __0 p) = (term363 __0 p).
Proof. exact (@lem16917 (term353 __0 p) (term363 __0 p) h1). Qed.
Lemma lem229672 (__0 : nat) (p : nat) : ((term354 __0 p) = (term358 __0 p)) = ((term353 __0 p) = (term363 __0 p)).
Proof. exact (prop_ext (fun h1 : (term354 __0 p) = (term358 __0 p) => @lem229671 __0 p h1) (fun h1 : (term353 __0 p) = (term363 __0 p) => @lem229670 __0 p)). Qed.
Lemma lem229673 (__0 : nat) (p : nat) : (term353 __0 p) = (term363 __0 p).
Proof. exact (EQ_MP (@lem229672 __0 p) (@lem229670 __0 p)). Qed.
Lemma lem229674 (__0 : nat) (p : nat) : term363 __0 p.
Proof. exact (EQ_MP (@lem229673 __0 p) (@lem229619 __0 p)). Qed.
Lemma lem229678 (p : nat) (h1 : p = (NUMERAL 0)) : (NUMERAL 0) = p.
Proof. exact (@lem229583 p h1 (@lem229576 p)). Qed.
Lemma lem229679 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term358 __0 p.
Proof. exact (h1). Qed.
Lemma lem229680 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term357 __0 p.
Proof. exact (@lem16684 (term209 __0) (term359 __0 p) h1). Qed.
Lemma lem229681 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term358 __0 p) = (term357 __0 p).
Proof. exact (prop_ext (fun h2 : term358 __0 p => @lem229680 __0 p h1) (fun h2 : term357 __0 p => @lem229679 __0 p h1)). Qed.
Lemma lem229682 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term357 __0 p.
Proof. exact (EQ_MP (@lem229681 __0 p h1) (@lem229679 __0 p h1)). Qed.
Lemma lem229683 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term278 __0.
Proof. exact (@lem16597 (term209 __0) (term359 __0 p) h1). Qed.
Lemma lem229684 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term358 __0 p) = (term278 __0).
Proof. exact (prop_ext (fun h2 : term358 __0 p => @lem229683 __0 p h1) (fun h2 : term278 __0 => @lem229679 __0 p h1)). Qed.
Lemma lem229685 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term278 __0.
Proof. exact (EQ_MP (@lem229684 __0 p h1) (@lem229679 __0 p h1)). Qed.
Lemma lem229686 (__0 : nat) (p : nat) (h1 : term357 __0 p) : term87 __0 p.
Proof. exact (@lem16684 (term343 p) (__0 = p) h1). Qed.
Lemma lem229687 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term357 __0 p) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term357 __0 p => @lem229686 __0 p h2) (fun h2 : term87 __0 p => @lem229682 __0 p h1)). Qed.
Lemma lem229688 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term87 __0 p.
Proof. exact (EQ_MP (@lem229687 __0 p h1) (@lem229682 __0 p h1)). Qed.
Lemma lem229689 (__0 : nat) (p : nat) (h1 : term357 __0 p) : term356 p.
Proof. exact (@lem16597 (term343 p) (__0 = p) h1). Qed.
Lemma lem229690 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term357 __0 p) = (term356 p).
Proof. exact (prop_ext (fun h2 : term357 __0 p => @lem229689 __0 p h2) (fun h2 : term356 p => @lem229682 __0 p h1)). Qed.
Lemma lem229691 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term356 p.
Proof. exact (EQ_MP (@lem229690 __0 p h1) (@lem229682 __0 p h1)). Qed.
Lemma lem229692 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term87 __0 p) : term364 __0 p.
Proof. exact (@lem16799 (term209 __0) (__0 = p) h1 h2). Qed.
Lemma lem229693 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term358 __0 p) : (term87 __0 p) = (term364 __0 p).
Proof. exact (prop_ext (fun h3 : term87 __0 p => @lem229692 __0 p h1 h3) (fun h3 : term364 __0 p => @lem229688 __0 p h2)). Qed.
Lemma lem229694 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term358 __0 p) : term364 __0 p.
Proof. exact (EQ_MP (@lem229693 __0 p h1 h2) (@lem229688 __0 p h2)). Qed.
Lemma lem229695 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term278 __0) = (term364 __0 p).
Proof. exact (prop_ext (fun h2 : term278 __0 => @lem229694 __0 p h2 h1) (fun h2 : term364 __0 p => @lem229685 __0 p h1)). Qed.
Lemma lem229696 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term364 __0 p.
Proof. exact (EQ_MP (@lem229695 __0 p h1) (@lem229685 __0 p h1)). Qed.
Lemma lem229697 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term364 __0 p) : term365 __0 p.
Proof. exact (@lem16799 (term343 p) (term366 __0 p) h1 h2). Qed.
Lemma lem229698 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term358 __0 p) : (term364 __0 p) = (term365 __0 p).
Proof. exact (prop_ext (fun h3 : term364 __0 p => @lem229697 __0 p h1 h3) (fun h3 : term365 __0 p => @lem229696 __0 p h2)). Qed.
Lemma lem229699 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term358 __0 p) : term365 __0 p.
Proof. exact (EQ_MP (@lem229698 __0 p h1 h2) (@lem229696 __0 p h2)). Qed.
Lemma lem229700 (__0 : nat) (p : nat) (h1 : term358 __0 p) : (term356 p) = (term365 __0 p).
Proof. exact (prop_ext (fun h2 : term356 p => @lem229699 __0 p h2 h1) (fun h2 : term365 __0 p => @lem229691 __0 p h1)). Qed.
Lemma lem229701 (__0 : nat) (p : nat) (h1 : term358 __0 p) : term365 __0 p.
Proof. exact (EQ_MP (@lem229700 __0 p h1) (@lem229691 __0 p h1)). Qed.
Lemma lem229702 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term365 __0 p.
Proof. exact (h1). Qed.
Lemma lem229703 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term364 __0 p.
Proof. exact (@lem16684 (term343 p) (term366 __0 p) h1). Qed.
Lemma lem229704 (__0 : nat) (p : nat) (h1 : term365 __0 p) : (term365 __0 p) = (term364 __0 p).
Proof. exact (prop_ext (fun h2 : term365 __0 p => @lem229703 __0 p h1) (fun h2 : term364 __0 p => @lem229702 __0 p h1)). Qed.
Lemma lem229705 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term364 __0 p.
Proof. exact (EQ_MP (@lem229704 __0 p h1) (@lem229702 __0 p h1)). Qed.
Lemma lem229706 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term356 p.
Proof. exact (@lem16597 (term343 p) (term366 __0 p) h1). Qed.
Lemma lem229707 (__0 : nat) (p : nat) (h1 : term365 __0 p) : (term365 __0 p) = (term356 p).
Proof. exact (prop_ext (fun h2 : term365 __0 p => @lem229706 __0 p h1) (fun h2 : term356 p => @lem229702 __0 p h1)). Qed.
Lemma lem229708 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term356 p.
Proof. exact (EQ_MP (@lem229707 __0 p h1) (@lem229702 __0 p h1)). Qed.
Lemma lem229709 (__0 : nat) (p : nat) (h1 : term364 __0 p) : term87 __0 p.
Proof. exact (@lem16684 (term209 __0) (__0 = p) h1). Qed.
Lemma lem229710 (__0 : nat) (p : nat) (h1 : term365 __0 p) : (term364 __0 p) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term364 __0 p => @lem229709 __0 p h2) (fun h2 : term87 __0 p => @lem229705 __0 p h1)). Qed.
Lemma lem229711 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term87 __0 p.
Proof. exact (EQ_MP (@lem229710 __0 p h1) (@lem229705 __0 p h1)). Qed.
Lemma lem229712 (__0 : nat) (p : nat) (h1 : term364 __0 p) : term278 __0.
Proof. exact (@lem16597 (term209 __0) (__0 = p) h1). Qed.
Lemma lem229713 (__0 : nat) (p : nat) (h1 : term365 __0 p) : (term364 __0 p) = (term278 __0).
Proof. exact (prop_ext (fun h2 : term364 __0 p => @lem229712 __0 p h2) (fun h2 : term278 __0 => @lem229705 __0 p h1)). Qed.
Lemma lem229714 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term278 __0.
Proof. exact (EQ_MP (@lem229713 __0 p h1) (@lem229705 __0 p h1)). Qed.
Lemma lem229715 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term87 __0 p) : term357 __0 p.
Proof. exact (@lem16799 (term343 p) (__0 = p) h1 h2). Qed.
Lemma lem229716 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term365 __0 p) : (term87 __0 p) = (term357 __0 p).
Proof. exact (prop_ext (fun h3 : term87 __0 p => @lem229715 __0 p h1 h3) (fun h3 : term357 __0 p => @lem229711 __0 p h2)). Qed.
Lemma lem229717 (__0 : nat) (p : nat) (h1 : term356 p) (h2 : term365 __0 p) : term357 __0 p.
Proof. exact (EQ_MP (@lem229716 __0 p h1 h2) (@lem229711 __0 p h2)). Qed.
Lemma lem229718 (__0 : nat) (p : nat) (h1 : term365 __0 p) : (term356 p) = (term357 __0 p).
Proof. exact (prop_ext (fun h2 : term356 p => @lem229717 __0 p h2 h1) (fun h2 : term357 __0 p => @lem229708 __0 p h1)). Qed.
Lemma lem229719 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term357 __0 p.
Proof. exact (EQ_MP (@lem229718 __0 p h1) (@lem229708 __0 p h1)). Qed.
Lemma lem229720 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term357 __0 p) : term358 __0 p.
Proof. exact (@lem16799 (term209 __0) (term359 __0 p) h1 h2). Qed.
Lemma lem229721 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term365 __0 p) : (term357 __0 p) = (term358 __0 p).
Proof. exact (prop_ext (fun h3 : term357 __0 p => @lem229720 __0 p h1 h3) (fun h3 : term358 __0 p => @lem229719 __0 p h2)). Qed.
Lemma lem229722 (__0 : nat) (p : nat) (h1 : term278 __0) (h2 : term365 __0 p) : term358 __0 p.
Proof. exact (EQ_MP (@lem229721 __0 p h1 h2) (@lem229719 __0 p h2)). Qed.
Lemma lem229723 (__0 : nat) (p : nat) (h1 : term365 __0 p) : (term278 __0) = (term358 __0 p).
Proof. exact (prop_ext (fun h2 : term278 __0 => @lem229722 __0 p h2 h1) (fun h2 : term358 __0 p => @lem229714 __0 p h1)). Qed.
Lemma lem229724 (__0 : nat) (p : nat) (h1 : term365 __0 p) : term358 __0 p.
Proof. exact (EQ_MP (@lem229723 __0 p h1) (@lem229714 __0 p h1)). Qed.
Lemma lem229725 (__0 : nat) (p : nat) : term367 __0 p.
Proof. exact (fun h0 : term365 __0 p => @lem229724 __0 p h0). Qed.
Lemma lem229726 (__0 : nat) (p : nat) : term368 __0 p.
Proof. exact (fun h0 : term358 __0 p => @lem229701 __0 p h0). Qed.
Lemma lem229727 (__0 : nat) (p : nat) : term369 __0 p.
Proof. exact (conj (@lem229726 __0 p) (@lem229725 __0 p)). Qed.
Lemma lem229728 (__0 : nat) (p : nat) : (term369 __0 p) = ((term358 __0 p) = (term365 __0 p)).
Proof. exact (@lem32 (term358 __0 p) (term365 __0 p)). Qed.
Lemma lem229729 (__0 : nat) (p : nat) : (term358 __0 p) = (term365 __0 p).
Proof. exact (EQ_MP (@lem229728 __0 p) (@lem229727 __0 p)). Qed.
Lemma lem229730 (__0 : nat) (p : nat) (h1 : (term358 __0 p) = (term365 __0 p)) : (term363 __0 p) = (term370 __0 p).
Proof. exact (@lem16917 (term363 __0 p) (term370 __0 p) h1). Qed.
Lemma lem229731 (__0 : nat) (p : nat) : ((term358 __0 p) = (term365 __0 p)) = ((term363 __0 p) = (term370 __0 p)).
Proof. exact (prop_ext (fun h1 : (term358 __0 p) = (term365 __0 p) => @lem229730 __0 p h1) (fun h1 : (term363 __0 p) = (term370 __0 p) => @lem229729 __0 p)). Qed.
Lemma lem229734 (__0 : nat) (p : nat) : (term363 __0 p) = (term370 __0 p).
Proof. exact (EQ_MP (@lem229731 __0 p) (@lem229729 __0 p)). Qed.
Lemma lem229735 (__0 : nat) (p : nat) : term370 __0 p.
Proof. exact (EQ_MP (@lem229734 __0 p) (@lem229674 __0 p)). Qed.
Lemma lem229736 (p : nat) : term371 p.
Proof. exact (@lem22025 ((NUMERAL 0) = p)). Qed.
Lemma lem229737 (p : nat) : (term371 p) = (term372 p).
Proof. exact (eq_refl (term371 p)). Qed.
Lemma lem229738 (p : nat) : term372 p.
Proof. exact (EQ_MP (@lem229737 p) (@lem229736 p)). Qed.
Lemma lem229739 (__0 : nat) (p : nat) : term373 __0 p.
Proof. exact (@lem229738 p (term366 __0 p)). Qed.
Lemma lem229740 (__0 : nat) (p : nat) : (term373 __0 p) = (term374 __0 p).
Proof. exact (eq_refl (term373 __0 p)). Qed.
Lemma lem229741 (__0 : nat) (p : nat) : term374 __0 p.
Proof. exact (EQ_MP (@lem229740 __0 p) (@lem229739 __0 p)). Qed.
Lemma lem229742 (__0 : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term375 __0 p.
Proof. exact (@lem229741 __0 p (@lem229678 p h1)). Qed.
Lemma lem229749 (__1 : nat) (__0 : nat) (h1 : term246) : term298 __1 __0.
Proof. exact (EQ_MP (@lem229450 __1 __0) (@lem229418 __1 __0 h1)). Qed.
Lemma lem229753 (__0 : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term366 __0 p.
Proof. exact (@lem229742 __0 p h1 (@lem229735 __0 p)). Qed.
Lemma lem229754 (__0 : nat) : term376 __0.
Proof. exact (@lem22288 (__0 = (NUMERAL 0))). Qed.
Lemma lem229755 (__0 : nat) : (term376 __0) = (term377 __0).
Proof. exact (eq_refl (term376 __0)). Qed.
Lemma lem229756 (__0 : nat) : term377 __0.
Proof. exact (EQ_MP (@lem229755 __0) (@lem229754 __0)). Qed.
Lemma lem229757 (__1 : nat) (__0 : nat) : term378 __1 __0.
Proof. exact (@lem229756 __0 (__1 = (term9 __1 __0))). Qed.
Lemma lem229758 (__1 : nat) (__0 : nat) : (term378 __1 __0) = (term379 __1 __0).
Proof. exact (eq_refl (term378 __1 __0)). Qed.
Lemma lem229759 (__1 : nat) (__0 : nat) : term379 __1 __0.
Proof. exact (EQ_MP (@lem229758 __1 __0) (@lem229757 __1 __0)). Qed.
Lemma lem229760 (__1 : nat) (__0 : nat) (p : nat) : term380 __1 __0 p.
Proof. exact (@lem229759 __1 __0 (__0 = p)). Qed.
Lemma lem229761 (__1 : nat) (__0 : nat) (p : nat) : (term380 __1 __0 p) = (term381 __1 __0 p).
Proof. exact (eq_refl (term380 __1 __0 p)). Qed.
Lemma lem229762 (__1 : nat) (__0 : nat) (p : nat) : term381 __1 __0 p.
Proof. exact (EQ_MP (@lem229761 __1 __0 p) (@lem229760 __1 __0 p)). Qed.
Lemma lem229763 (__1 : nat) (__0 : nat) (p : nat) (h1 : term246) : term382 __1 __0 p.
Proof. exact (@lem229762 __1 __0 p (@lem229749 __1 __0 h1)). Qed.
Lemma lem229764 (__1 : nat) (__0 : nat) (p : nat) (h1 : term246) (h2 : p = (NUMERAL 0)) : term383 __1 __0 p.
Proof. exact (@lem229763 __1 __0 p h1 (@lem229753 __0 p h2)). Qed.
Lemma lem229765 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term384 __1 __0 p.
Proof. exact (h1). Qed.
Lemma lem229766 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term87 __0 p.
Proof. exact (@lem16684 (__1 = (term9 __1 __0)) (__0 = p) h1). Qed.
Lemma lem229767 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : (term384 __1 __0 p) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term384 __1 __0 p => @lem229766 __1 __0 p h1) (fun h2 : term87 __0 p => @lem229765 __1 __0 p h1)). Qed.
Lemma lem229768 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term87 __0 p.
Proof. exact (EQ_MP (@lem229767 __1 __0 p h1) (@lem229765 __1 __0 p h1)). Qed.
Lemma lem229769 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term300 __1 __0.
Proof. exact (@lem16597 (__1 = (term9 __1 __0)) (__0 = p) h1). Qed.
Lemma lem229770 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : (term384 __1 __0 p) = (term300 __1 __0).
Proof. exact (prop_ext (fun h2 : term384 __1 __0 p => @lem229769 __1 __0 p h1) (fun h2 : term300 __1 __0 => @lem229765 __1 __0 p h1)). Qed.
Lemma lem229771 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term300 __1 __0.
Proof. exact (EQ_MP (@lem229770 __1 __0 p h1) (@lem229765 __1 __0 p h1)). Qed.
Lemma lem229772 (p : nat) (__1 : nat) (__0 : nat) (h1 : term87 __0 p) (h2 : term300 __1 __0) : term385 p __1 __0.
Proof. exact (@lem16799 (__0 = p) (__1 = (term9 __1 __0)) h1 h2). Qed.
Lemma lem229773 (__1 : nat) (__0 : nat) (p : nat) (h1 : term87 __0 p) (h2 : term384 __1 __0 p) : (term300 __1 __0) = (term385 p __1 __0).
Proof. exact (prop_ext (fun h3 : term300 __1 __0 => @lem229772 p __1 __0 h1 h3) (fun h3 : term385 p __1 __0 => @lem229771 __1 __0 p h2)). Qed.
Lemma lem229774 (__1 : nat) (__0 : nat) (p : nat) (h1 : term87 __0 p) (h2 : term384 __1 __0 p) : term385 p __1 __0.
Proof. exact (EQ_MP (@lem229773 __1 __0 p h1 h2) (@lem229771 __1 __0 p h2)). Qed.
Lemma lem229775 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : (term87 __0 p) = (term385 p __1 __0).
Proof. exact (prop_ext (fun h2 : term87 __0 p => @lem229774 __1 __0 p h2 h1) (fun h2 : term385 p __1 __0 => @lem229768 __1 __0 p h1)). Qed.
Lemma lem229776 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term385 p __1 __0.
Proof. exact (EQ_MP (@lem229775 __1 __0 p h1) (@lem229768 __1 __0 p h1)). Qed.
Lemma lem229777 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term385 p __1 __0.
Proof. exact (h1). Qed.
Lemma lem229778 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term300 __1 __0.
Proof. exact (@lem16684 (__0 = p) (__1 = (term9 __1 __0)) h1). Qed.
Lemma lem229779 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : (term385 p __1 __0) = (term300 __1 __0).
Proof. exact (prop_ext (fun h2 : term385 p __1 __0 => @lem229778 p __1 __0 h1) (fun h2 : term300 __1 __0 => @lem229777 p __1 __0 h1)). Qed.
Lemma lem229780 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term300 __1 __0.
Proof. exact (EQ_MP (@lem229779 p __1 __0 h1) (@lem229777 p __1 __0 h1)). Qed.
Lemma lem229781 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term87 __0 p.
Proof. exact (@lem16597 (__0 = p) (__1 = (term9 __1 __0)) h1). Qed.
Lemma lem229782 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : (term385 p __1 __0) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term385 p __1 __0 => @lem229781 p __1 __0 h1) (fun h2 : term87 __0 p => @lem229777 p __1 __0 h1)). Qed.
Lemma lem229783 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term87 __0 p.
Proof. exact (EQ_MP (@lem229782 p __1 __0 h1) (@lem229777 p __1 __0 h1)). Qed.
Lemma lem229784 (p : nat) (__1 : nat) (__0 : nat) (h1 : term87 __0 p) (h2 : term300 __1 __0) : term384 __1 __0 p.
Proof. exact (@lem16799 (__1 = (term9 __1 __0)) (__0 = p) h2 h1). Qed.
Lemma lem229785 (p : nat) (__1 : nat) (__0 : nat) (h1 : term300 __1 __0) (h2 : term385 p __1 __0) : (term87 __0 p) = (term384 __1 __0 p).
Proof. exact (prop_ext (fun h3 : term87 __0 p => @lem229784 p __1 __0 h3 h1) (fun h3 : term384 __1 __0 p => @lem229783 p __1 __0 h2)). Qed.
Lemma lem229786 (p : nat) (__1 : nat) (__0 : nat) (h1 : term300 __1 __0) (h2 : term385 p __1 __0) : term384 __1 __0 p.
Proof. exact (EQ_MP (@lem229785 p __1 __0 h1 h2) (@lem229783 p __1 __0 h2)). Qed.
Lemma lem229787 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : (term300 __1 __0) = (term384 __1 __0 p).
Proof. exact (prop_ext (fun h2 : term300 __1 __0 => @lem229786 p __1 __0 h2 h1) (fun h2 : term384 __1 __0 p => @lem229780 p __1 __0 h1)). Qed.
Lemma lem229788 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term384 __1 __0 p.
Proof. exact (EQ_MP (@lem229787 p __1 __0 h1) (@lem229780 p __1 __0 h1)). Qed.
Lemma lem229789 (__1 : nat) (__0 : nat) (p : nat) : term386 __1 __0 p.
Proof. exact (fun h0 : term385 p __1 __0 => @lem229788 p __1 __0 h0). Qed.
Lemma lem229790 (p : nat) (__1 : nat) (__0 : nat) : term387 p __1 __0.
Proof. exact (fun h0 : term384 __1 __0 p => @lem229776 __1 __0 p h0). Qed.
Lemma lem229791 (__1 : nat) (__0 : nat) (p : nat) : term388 __1 __0 p.
Proof. exact (conj (@lem229790 p __1 __0) (@lem229789 __1 __0 p)). Qed.
Lemma lem229792 (p : nat) (__1 : nat) (__0 : nat) : (term388 __1 __0 p) = ((term384 __1 __0 p) = (term385 p __1 __0)).
Proof. exact (@lem32 (term384 __1 __0 p) (term385 p __1 __0)). Qed.
Lemma lem229793 (p : nat) (__1 : nat) (__0 : nat) : (term384 __1 __0 p) = (term385 p __1 __0).
Proof. exact (EQ_MP (@lem229792 p __1 __0) (@lem229791 __1 __0 p)). Qed.
Lemma lem229794 (p : nat) (__1 : nat) (__0 : nat) (h1 : (term384 __1 __0 p) = (term385 p __1 __0)) : (term383 __1 __0 p) = (term389 p __1 __0).
Proof. exact (@lem16917 (term383 __1 __0 p) (term389 p __1 __0) h1). Qed.
Lemma lem229795 (p : nat) (__1 : nat) (__0 : nat) : ((term384 __1 __0 p) = (term385 p __1 __0)) = ((term383 __1 __0 p) = (term389 p __1 __0)).
Proof. exact (prop_ext (fun h1 : (term384 __1 __0 p) = (term385 p __1 __0) => @lem229794 p __1 __0 h1) (fun h1 : (term383 __1 __0 p) = (term389 p __1 __0) => @lem229793 p __1 __0)). Qed.
Lemma lem229796 (p : nat) (__1 : nat) (__0 : nat) : (term383 __1 __0 p) = (term389 p __1 __0).
Proof. exact (EQ_MP (@lem229795 p __1 __0) (@lem229793 p __1 __0)). Qed.
Lemma lem229797 (__1 : nat) (__0 : nat) (p : nat) (h1 : term246) (h2 : p = (NUMERAL 0)) : term389 p __1 __0.
Proof. exact (EQ_MP (@lem229796 p __1 __0) (@lem229764 __1 __0 p h1 h2)). Qed.
Lemma lem229803 {_12885 : Type'} (__x : _12885) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem229805 {_12887 : Type'} (__x : _12887) (h1 : __x = __x) : __x = __x.
Proof. exact (h1). Qed.
Lemma lem229807 {_12887 : Type'} (__x : _12887) (__y : _12887) (h1 : __x = __y) : __x = __y.
Proof. exact (h1). Qed.
Lemma lem229808 {_12887 : Type'} : (@eq _12887) = (@eq _12887).
Proof. exact (eq_refl (@eq _12887)). Qed.
Lemma lem229809 {_12887 : Type'} (__x : _12887) (__y : _12887) (h1 : __x = __y) : (@eq _12887 __x) = (@eq _12887 __y).
Proof. exact (MK_COMB (@lem229808 _12887) (@lem229807 _12887 __x __y h1)). Qed.
Lemma lem229810 {_12887 : Type'} (__x : _12887) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem229811 {_12887 : Type'} (__x : _12887) (__y : _12887) (h1 : __x = __y) : (__x = __x) = (__y = __x).
Proof. exact (MK_COMB (@lem229809 _12887 __x __y h1) (@lem229810 _12887 __x)). Qed.
Lemma lem229812 {_12887 : Type'} (__x : _12887) (__y : _12887) (h1 : __x = __x) (h2 : __x = __y) : __y = __x.
Proof. exact (EQ_MP (@lem229811 _12887 __x __y h2) (@lem229805 _12887 __x h1)). Qed.
Lemma lem229813 {_12887 : Type'} (__x : _12887) (__y : _12887) (h1 : __x = __y) : term307 _12887 __y __x.
Proof. exact (fun h0 : __x = __x => @lem229812 _12887 __x __y h0 h1). Qed.
Lemma lem229814 {_12887 : Type'} (__x : _12887) : term308 _12887 __x.
Proof. exact (@lem22518 (__x = __x)). Qed.
Lemma lem229815 {_12887 : Type'} (__x : _12887) : (term308 _12887 __x) = (term309 _12887 __x).
Proof. exact (eq_refl (term308 _12887 __x)). Qed.
Lemma lem229816 {_12887 : Type'} (__x : _12887) : term309 _12887 __x.
Proof. exact (EQ_MP (@lem229815 _12887 __x) (@lem229814 _12887 __x)). Qed.
Lemma lem229817 {_12887 : Type'} (__y : _12887) (__x : _12887) : term310 _12887 __y __x.
Proof. exact (@lem229816 _12887 __x (__y = __x)). Qed.
Lemma lem229818 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term310 _12887 __y __x) = ((term307 _12887 __y __x) = (term311 _12887 __y __x)).
Proof. exact (eq_refl (term310 _12887 __y __x)). Qed.
Lemma lem229821 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term307 _12887 __y __x) = (term311 _12887 __y __x).
Proof. exact (EQ_MP (@lem229818 _12887 __y __x) (@lem229817 _12887 __y __x)). Qed.
Lemma lem229822 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term307 _12887 __y __x) = (term311 _12887 __y __x).
Proof. exact (@lem229821 _12887 __y __x). Qed.
Lemma lem229823 {_12887 : Type'} (__x : _12887) (__y : _12887) (h1 : __x = __y) : term311 _12887 __y __x.
Proof. exact (EQ_MP (@lem229822 _12887 __y __x) (@lem229813 _12887 __x __y h1)). Qed.
Lemma lem229824 {_12887 : Type'} (__y : _12887) (__x : _12887) : term312 _12887 __y __x.
Proof. exact (fun h0 : __x = __y => @lem229823 _12887 __x __y h0). Qed.
Lemma lem229825 {_12887 : Type'} (__x : _12887) (__y : _12887) : term313 _12887 __x __y.
Proof. exact (@lem22518 (__x = __y)). Qed.
Lemma lem229826 {_12887 : Type'} (__x : _12887) (__y : _12887) : (term313 _12887 __x __y) = (term314 _12887 __x __y).
Proof. exact (eq_refl (term313 _12887 __x __y)). Qed.
Lemma lem229827 {_12887 : Type'} (__x : _12887) (__y : _12887) : term314 _12887 __x __y.
Proof. exact (EQ_MP (@lem229826 _12887 __x __y) (@lem229825 _12887 __x __y)). Qed.
Lemma lem229828 {_12887 : Type'} (__y : _12887) (__x : _12887) : term315 _12887 __y __x.
Proof. exact (@lem229827 _12887 __x __y (term311 _12887 __y __x)). Qed.
Lemma lem229829 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term315 _12887 __y __x) = ((term312 _12887 __y __x) = (term316 _12887 __y __x)).
Proof. exact (eq_refl (term315 _12887 __y __x)). Qed.
Lemma lem229832 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term312 _12887 __y __x) = (term316 _12887 __y __x).
Proof. exact (EQ_MP (@lem229829 _12887 __y __x) (@lem229828 _12887 __y __x)). Qed.
Lemma lem229833 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term312 _12887 __y __x) = (term316 _12887 __y __x).
Proof. exact (@lem229832 _12887 __y __x). Qed.
Lemma lem229834 {_12887 : Type'} (__y : _12887) (__x : _12887) : term316 _12887 __y __x.
Proof. exact (EQ_MP (@lem229833 _12887 __y __x) (@lem229824 _12887 __y __x)). Qed.
Lemma lem229835 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term317 _12887 __y __x.
Proof. exact (h1). Qed.
Lemma lem229836 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term318 _12887 __y __x.
Proof. exact (@lem16684 (term319 _12887 __x __y) (term311 _12887 __y __x) h1). Qed.
Lemma lem229837 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : (term317 _12887 __y __x) = (term318 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term317 _12887 __y __x => @lem229836 _12887 __y __x h1) (fun h2 : term318 _12887 __y __x => @lem229835 _12887 __y __x h1)). Qed.
Lemma lem229838 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term318 _12887 __y __x.
Proof. exact (EQ_MP (@lem229837 _12887 __y __x h1) (@lem229835 _12887 __y __x h1)). Qed.
Lemma lem229839 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term320 _12887 __x __y.
Proof. exact (@lem16597 (term319 _12887 __x __y) (term311 _12887 __y __x) h1). Qed.
Lemma lem229840 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : (term317 _12887 __y __x) = (term320 _12887 __x __y).
Proof. exact (prop_ext (fun h2 : term317 _12887 __y __x => @lem229839 _12887 __y __x h1) (fun h2 : term320 _12887 __x __y => @lem229835 _12887 __y __x h1)). Qed.
Lemma lem229841 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term320 _12887 __x __y.
Proof. exact (EQ_MP (@lem229840 _12887 __y __x h1) (@lem229835 _12887 __y __x h1)). Qed.
Lemma lem229842 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term318 _12887 __y __x) : term319 _12887 __y __x.
Proof. exact (@lem16684 (term321 _12887 __x) (__y = __x) h1). Qed.
Lemma lem229843 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : (term318 _12887 __y __x) = (term319 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term318 _12887 __y __x => @lem229842 _12887 __y __x h2) (fun h2 : term319 _12887 __y __x => @lem229838 _12887 __y __x h1)). Qed.
Lemma lem229844 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term319 _12887 __y __x.
Proof. exact (EQ_MP (@lem229843 _12887 __y __x h1) (@lem229838 _12887 __y __x h1)). Qed.
Lemma lem229845 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term318 _12887 __y __x) : term322 _12887 __x.
Proof. exact (@lem16597 (term321 _12887 __x) (__y = __x) h1). Qed.
Lemma lem229846 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : (term318 _12887 __y __x) = (term322 _12887 __x).
Proof. exact (prop_ext (fun h2 : term318 _12887 __y __x => @lem229845 _12887 __y __x h2) (fun h2 : term322 _12887 __x => @lem229838 _12887 __y __x h1)). Qed.
Lemma lem229847 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term322 _12887 __x.
Proof. exact (EQ_MP (@lem229846 _12887 __y __x h1) (@lem229838 _12887 __y __x h1)). Qed.
Lemma lem229848 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term320 _12887 __x __y) (h2 : term319 _12887 __y __x) : term323 _12887 __y __x.
Proof. exact (@lem16799 (term319 _12887 __x __y) (__y = __x) h1 h2). Qed.
Lemma lem229849 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term320 _12887 __x __y) (h2 : term317 _12887 __y __x) : (term319 _12887 __y __x) = (term323 _12887 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _12887 __y __x => @lem229848 _12887 __y __x h1 h3) (fun h3 : term323 _12887 __y __x => @lem229844 _12887 __y __x h2)). Qed.
Lemma lem229850 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term320 _12887 __x __y) (h2 : term317 _12887 __y __x) : term323 _12887 __y __x.
Proof. exact (EQ_MP (@lem229849 _12887 __y __x h1 h2) (@lem229844 _12887 __y __x h2)). Qed.
Lemma lem229851 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : (term320 _12887 __x __y) = (term323 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _12887 __x __y => @lem229850 _12887 __y __x h2 h1) (fun h2 : term323 _12887 __y __x => @lem229841 _12887 __y __x h1)). Qed.
Lemma lem229852 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term323 _12887 __y __x.
Proof. exact (EQ_MP (@lem229851 _12887 __y __x h1) (@lem229841 _12887 __y __x h1)). Qed.
Lemma lem229853 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term322 _12887 __x) (h2 : term323 _12887 __y __x) : term324 _12887 __y __x.
Proof. exact (@lem16799 (term321 _12887 __x) (term325 _12887 __y __x) h1 h2). Qed.
Lemma lem229854 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term322 _12887 __x) (h2 : term317 _12887 __y __x) : (term323 _12887 __y __x) = (term324 _12887 __y __x).
Proof. exact (prop_ext (fun h3 : term323 _12887 __y __x => @lem229853 _12887 __y __x h1 h3) (fun h3 : term324 _12887 __y __x => @lem229852 _12887 __y __x h2)). Qed.
Lemma lem229855 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term322 _12887 __x) (h2 : term317 _12887 __y __x) : term324 _12887 __y __x.
Proof. exact (EQ_MP (@lem229854 _12887 __y __x h1 h2) (@lem229852 _12887 __y __x h2)). Qed.
Lemma lem229856 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : (term322 _12887 __x) = (term324 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _12887 __x => @lem229855 _12887 __y __x h2 h1) (fun h2 : term324 _12887 __y __x => @lem229847 _12887 __y __x h1)). Qed.
Lemma lem229857 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term317 _12887 __y __x) : term324 _12887 __y __x.
Proof. exact (EQ_MP (@lem229856 _12887 __y __x h1) (@lem229847 _12887 __y __x h1)). Qed.
Lemma lem229858 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term324 _12887 __y __x.
Proof. exact (h1). Qed.
Lemma lem229859 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term323 _12887 __y __x.
Proof. exact (@lem16684 (term321 _12887 __x) (term325 _12887 __y __x) h1). Qed.
Lemma lem229860 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : (term324 _12887 __y __x) = (term323 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term324 _12887 __y __x => @lem229859 _12887 __y __x h1) (fun h2 : term323 _12887 __y __x => @lem229858 _12887 __y __x h1)). Qed.
Lemma lem229861 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term323 _12887 __y __x.
Proof. exact (EQ_MP (@lem229860 _12887 __y __x h1) (@lem229858 _12887 __y __x h1)). Qed.
Lemma lem229862 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term322 _12887 __x.
Proof. exact (@lem16597 (term321 _12887 __x) (term325 _12887 __y __x) h1). Qed.
Lemma lem229863 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : (term324 _12887 __y __x) = (term322 _12887 __x).
Proof. exact (prop_ext (fun h2 : term324 _12887 __y __x => @lem229862 _12887 __y __x h1) (fun h2 : term322 _12887 __x => @lem229858 _12887 __y __x h1)). Qed.
Lemma lem229864 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term322 _12887 __x.
Proof. exact (EQ_MP (@lem229863 _12887 __y __x h1) (@lem229858 _12887 __y __x h1)). Qed.
Lemma lem229865 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term323 _12887 __y __x) : term319 _12887 __y __x.
Proof. exact (@lem16684 (term319 _12887 __x __y) (__y = __x) h1). Qed.
Lemma lem229866 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : (term323 _12887 __y __x) = (term319 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term323 _12887 __y __x => @lem229865 _12887 __y __x h2) (fun h2 : term319 _12887 __y __x => @lem229861 _12887 __y __x h1)). Qed.
Lemma lem229867 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term319 _12887 __y __x.
Proof. exact (EQ_MP (@lem229866 _12887 __y __x h1) (@lem229861 _12887 __y __x h1)). Qed.
Lemma lem229868 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term323 _12887 __y __x) : term320 _12887 __x __y.
Proof. exact (@lem16597 (term319 _12887 __x __y) (__y = __x) h1). Qed.
Lemma lem229869 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : (term323 _12887 __y __x) = (term320 _12887 __x __y).
Proof. exact (prop_ext (fun h2 : term323 _12887 __y __x => @lem229868 _12887 __y __x h2) (fun h2 : term320 _12887 __x __y => @lem229861 _12887 __y __x h1)). Qed.
Lemma lem229870 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term320 _12887 __x __y.
Proof. exact (EQ_MP (@lem229869 _12887 __y __x h1) (@lem229861 _12887 __y __x h1)). Qed.
Lemma lem229871 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term322 _12887 __x) (h2 : term319 _12887 __y __x) : term318 _12887 __y __x.
Proof. exact (@lem16799 (term321 _12887 __x) (__y = __x) h1 h2). Qed.
Lemma lem229872 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term322 _12887 __x) (h2 : term324 _12887 __y __x) : (term319 _12887 __y __x) = (term318 _12887 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _12887 __y __x => @lem229871 _12887 __y __x h1 h3) (fun h3 : term318 _12887 __y __x => @lem229867 _12887 __y __x h2)). Qed.
Lemma lem229873 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term322 _12887 __x) (h2 : term324 _12887 __y __x) : term318 _12887 __y __x.
Proof. exact (EQ_MP (@lem229872 _12887 __y __x h1 h2) (@lem229867 _12887 __y __x h2)). Qed.
Lemma lem229874 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : (term322 _12887 __x) = (term318 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _12887 __x => @lem229873 _12887 __y __x h2 h1) (fun h2 : term318 _12887 __y __x => @lem229864 _12887 __y __x h1)). Qed.
Lemma lem229875 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term318 _12887 __y __x.
Proof. exact (EQ_MP (@lem229874 _12887 __y __x h1) (@lem229864 _12887 __y __x h1)). Qed.
Lemma lem229876 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term320 _12887 __x __y) (h2 : term318 _12887 __y __x) : term317 _12887 __y __x.
Proof. exact (@lem16799 (term319 _12887 __x __y) (term311 _12887 __y __x) h1 h2). Qed.
Lemma lem229877 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term320 _12887 __x __y) (h2 : term324 _12887 __y __x) : (term318 _12887 __y __x) = (term317 _12887 __y __x).
Proof. exact (prop_ext (fun h3 : term318 _12887 __y __x => @lem229876 _12887 __y __x h1 h3) (fun h3 : term317 _12887 __y __x => @lem229875 _12887 __y __x h2)). Qed.
Lemma lem229878 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term320 _12887 __x __y) (h2 : term324 _12887 __y __x) : term317 _12887 __y __x.
Proof. exact (EQ_MP (@lem229877 _12887 __y __x h1 h2) (@lem229875 _12887 __y __x h2)). Qed.
Lemma lem229879 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : (term320 _12887 __x __y) = (term317 _12887 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _12887 __x __y => @lem229878 _12887 __y __x h2 h1) (fun h2 : term317 _12887 __y __x => @lem229870 _12887 __y __x h1)). Qed.
Lemma lem229880 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : term324 _12887 __y __x) : term317 _12887 __y __x.
Proof. exact (EQ_MP (@lem229879 _12887 __y __x h1) (@lem229870 _12887 __y __x h1)). Qed.
Lemma lem229881 {_12887 : Type'} (__y : _12887) (__x : _12887) : term326 _12887 __y __x.
Proof. exact (fun h0 : term324 _12887 __y __x => @lem229880 _12887 __y __x h0). Qed.
Lemma lem229882 {_12887 : Type'} (__y : _12887) (__x : _12887) : term327 _12887 __y __x.
Proof. exact (fun h0 : term317 _12887 __y __x => @lem229857 _12887 __y __x h0). Qed.
Lemma lem229883 {_12887 : Type'} (__y : _12887) (__x : _12887) : term328 _12887 __y __x.
Proof. exact (conj (@lem229882 _12887 __y __x) (@lem229881 _12887 __y __x)). Qed.
Lemma lem229884 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term328 _12887 __y __x) = ((term317 _12887 __y __x) = (term324 _12887 __y __x)).
Proof. exact (@lem32 (term317 _12887 __y __x) (term324 _12887 __y __x)). Qed.
Lemma lem229885 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term317 _12887 __y __x) = (term324 _12887 __y __x).
Proof. exact (EQ_MP (@lem229884 _12887 __y __x) (@lem229883 _12887 __y __x)). Qed.
Lemma lem229886 {_12887 : Type'} (__y : _12887) (__x : _12887) (h1 : (term317 _12887 __y __x) = (term324 _12887 __y __x)) : (term316 _12887 __y __x) = (term329 _12887 __y __x).
Proof. exact (@lem16917 (term316 _12887 __y __x) (term329 _12887 __y __x) h1). Qed.
Lemma lem229887 {_12887 : Type'} (__y : _12887) (__x : _12887) : ((term317 _12887 __y __x) = (term324 _12887 __y __x)) = ((term316 _12887 __y __x) = (term329 _12887 __y __x)).
Proof. exact (prop_ext (fun h1 : (term317 _12887 __y __x) = (term324 _12887 __y __x) => @lem229886 _12887 __y __x h1) (fun h1 : (term316 _12887 __y __x) = (term329 _12887 __y __x) => @lem229885 _12887 __y __x)). Qed.
Lemma lem229888 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term316 _12887 __y __x) = (term329 _12887 __y __x).
Proof. exact (EQ_MP (@lem229887 _12887 __y __x) (@lem229885 _12887 __y __x)). Qed.
Lemma lem229889 {_12887 : Type'} (__y : _12887) (__x : _12887) : term329 _12887 __y __x.
Proof. exact (EQ_MP (@lem229888 _12887 __y __x) (@lem229834 _12887 __y __x)). Qed.
Lemma lem229890 {_12887 : Type'} (__y : _12887) (__x : _12887) : term329 _12887 __y __x.
Proof. exact (@lem229889 _12887 __y __x). Qed.
Lemma lem229891 {_12887 : Type'} (__x : _12887) : __x = __x.
Proof. exact (@lem229803 _12887 __x). Qed.
Lemma lem229894 {_12887 : Type'} (__x : _12887) : (__x = __x) = (__x = __x).
Proof. exact (eq_refl (__x = __x)). Qed.
Lemma lem229895 {_12887 : Type'} (__x : _12887) : (__x = __x) = (__x = __x).
Proof. exact (@lem229894 _12887 __x). Qed.
Lemma lem229896 {_12887 : Type'} (__x : _12887) : __x = __x.
Proof. exact (EQ_MP (@lem229895 _12887 __x) (@lem229891 _12887 __x)). Qed.
Lemma lem229899 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term329 _12887 __y __x) = (term329 _12887 __y __x).
Proof. exact (eq_refl (term329 _12887 __y __x)). Qed.
Lemma lem229900 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term329 _12887 __y __x) = (term329 _12887 __y __x).
Proof. exact (@lem229899 _12887 __y __x). Qed.
Lemma lem229901 {_12887 : Type'} (__y : _12887) (__x : _12887) : term329 _12887 __y __x.
Proof. exact (EQ_MP (@lem229900 _12887 __y __x) (@lem229890 _12887 __y __x)). Qed.
Lemma lem229902 {_12887 : Type'} (__x : _12887) : term330 _12887 __x.
Proof. exact (@lem22025 (__x = __x)). Qed.
Lemma lem229903 {_12887 : Type'} (__x : _12887) : (term330 _12887 __x) = (term331 _12887 __x).
Proof. exact (eq_refl (term330 _12887 __x)). Qed.
Lemma lem229904 {_12887 : Type'} (__x : _12887) : term331 _12887 __x.
Proof. exact (EQ_MP (@lem229903 _12887 __x) (@lem229902 _12887 __x)). Qed.
Lemma lem229905 {_12887 : Type'} (__y : _12887) (__x : _12887) : term332 _12887 __y __x.
Proof. exact (@lem229904 _12887 __x (term325 _12887 __y __x)). Qed.
Lemma lem229906 {_12887 : Type'} (__y : _12887) (__x : _12887) : (term332 _12887 __y __x) = (term333 _12887 __y __x).
Proof. exact (eq_refl (term332 _12887 __y __x)). Qed.
Lemma lem229907 {_12887 : Type'} (__y : _12887) (__x : _12887) : term333 _12887 __y __x.
Proof. exact (EQ_MP (@lem229906 _12887 __y __x) (@lem229905 _12887 __y __x)). Qed.
Lemma lem229908 {_12887 : Type'} (__y : _12887) (__x : _12887) : term334 _12887 __y __x.
Proof. exact (@lem229907 _12887 __y __x (@lem229896 _12887 __x)). Qed.
Lemma lem229911 {_12887 : Type'} (__y : _12887) (__x : _12887) : term325 _12887 __y __x.
Proof. exact (@lem229908 _12887 __y __x (@lem229901 _12887 __y __x)). Qed.
Lemma lem229912 (__y : nat) (__x : nat) : term335 __y __x.
Proof. exact (@lem229911 nat __y __x). Qed.
Lemma lem229919 (__3 : nat) (__2 : nat) (h1 : term277) : (Nat.mul __2 __3) = (Nat.mul __3 __2).
Proof. exact (@lem229408 __3 __2 h1). Qed.
Lemma lem229923 (__2 : nat) (__3 : nat) : term390 __2 __3.
Proof. exact (@lem229912 (Nat.mul __3 __2) (Nat.mul __2 __3)). Qed.
Lemma lem229924 (__3 : nat) (__2 : nat) : term391 __3 __2.
Proof. exact (@lem22025 ((Nat.mul __2 __3) = (Nat.mul __3 __2))). Qed.
Lemma lem229925 (__3 : nat) (__2 : nat) : (term391 __3 __2) = (term392 __3 __2).
Proof. exact (eq_refl (term391 __3 __2)). Qed.
Lemma lem229926 (__3 : nat) (__2 : nat) : term392 __3 __2.
Proof. exact (EQ_MP (@lem229925 __3 __2) (@lem229924 __3 __2)). Qed.
Lemma lem229927 (__2 : nat) (__3 : nat) : term393 __2 __3.
Proof. exact (@lem229926 __3 __2 ((Nat.mul __3 __2) = (Nat.mul __2 __3))). Qed.
Lemma lem229928 (__2 : nat) (__3 : nat) : (term393 __2 __3) = (term394 __2 __3).
Proof. exact (eq_refl (term393 __2 __3)). Qed.
Lemma lem229929 (__2 : nat) (__3 : nat) : term394 __2 __3.
Proof. exact (EQ_MP (@lem229928 __2 __3) (@lem229927 __2 __3)). Qed.
Lemma lem229930 (__2 : nat) (__3 : nat) (h1 : term277) : term395 __2 __3.
Proof. exact (@lem229929 __2 __3 (@lem229919 __3 __2 h1)). Qed.
Lemma lem229933 (__2 : nat) (__3 : nat) (h1 : term277) : (Nat.mul __3 __2) = (Nat.mul __2 __3).
Proof. exact (@lem229930 __2 __3 h1 (@lem229923 __2 __3)). Qed.
Lemma lem229941 (__1 : nat) (__0 : nat) (h1 : (term9 __1 __0) = (term9 __1 __0)) : (term9 __1 __0) = (term9 __1 __0).
Proof. exact (h1). Qed.
Lemma lem229943 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) : (term396 __1 __0) = (term236 __1 __0).
Proof. exact (h1). Qed.
Lemma lem229944 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem229945 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) : (term397 __1 __0) = (term237 __1 __0).
Proof. exact (MK_COMB (@lem229944) (@lem229943 __1 __0 h1)). Qed.
Lemma lem229946 (__1 : nat) (__0 : nat) : (Nat.modulo __1 __0) = (Nat.modulo __1 __0).
Proof. exact (eq_refl (Nat.modulo __1 __0)). Qed.
Lemma lem229947 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) : (term9 __1 __0) = (term4 __1 __0).
Proof. exact (MK_COMB (@lem229945 __1 __0 h1) (@lem229946 __1 __0)). Qed.
Lemma lem229948 (__1 : nat) (__0 : nat) : (term398 __1 __0) = (term398 __1 __0).
Proof. exact (eq_refl (term398 __1 __0)). Qed.
Lemma lem229949 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) : ((term9 __1 __0) = (term9 __1 __0)) = ((term9 __1 __0) = (term4 __1 __0)).
Proof. exact (MK_COMB (@lem229948 __1 __0) (@lem229947 __1 __0 h1)). Qed.
Lemma lem229950 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) (h2 : (term9 __1 __0) = (term9 __1 __0)) : (term9 __1 __0) = (term4 __1 __0).
Proof. exact (EQ_MP (@lem229949 __1 __0 h1) (@lem229941 __1 __0 h2)). Qed.
Lemma lem229951 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) : term399 __1 __0.
Proof. exact (fun h0 : (term9 __1 __0) = (term9 __1 __0) => @lem229950 __1 __0 h1 h0). Qed.
Lemma lem229952 (__1 : nat) (__0 : nat) : term400 __1 __0.
Proof. exact (@lem22518 ((term9 __1 __0) = (term9 __1 __0))). Qed.
Lemma lem229953 (__1 : nat) (__0 : nat) : (term400 __1 __0) = (term401 __1 __0).
Proof. exact (eq_refl (term400 __1 __0)). Qed.
Lemma lem229954 (__1 : nat) (__0 : nat) : term401 __1 __0.
Proof. exact (EQ_MP (@lem229953 __1 __0) (@lem229952 __1 __0)). Qed.
Lemma lem229955 (__1 : nat) (__0 : nat) : term402 __1 __0.
Proof. exact (@lem229954 __1 __0 ((term9 __1 __0) = (term4 __1 __0))). Qed.
Lemma lem229956 (__1 : nat) (__0 : nat) : (term402 __1 __0) = ((term399 __1 __0) = (term403 __1 __0)).
Proof. exact (eq_refl (term402 __1 __0)). Qed.
Lemma lem229959 (__1 : nat) (__0 : nat) : (term399 __1 __0) = (term403 __1 __0).
Proof. exact (EQ_MP (@lem229956 __1 __0) (@lem229955 __1 __0)). Qed.
Lemma lem229960 (__1 : nat) (__0 : nat) (h1 : (term396 __1 __0) = (term236 __1 __0)) : term403 __1 __0.
Proof. exact (EQ_MP (@lem229959 __1 __0) (@lem229951 __1 __0 h1)). Qed.
Lemma lem229961 (__1 : nat) (__0 : nat) : term404 __1 __0.
Proof. exact (fun h0 : (term396 __1 __0) = (term236 __1 __0) => @lem229960 __1 __0 h0). Qed.
Lemma lem229962 (__1 : nat) (__0 : nat) : term405 __1 __0.
Proof. exact (@lem22518 ((term396 __1 __0) = (term236 __1 __0))). Qed.
Lemma lem229963 (__1 : nat) (__0 : nat) : (term405 __1 __0) = (term406 __1 __0).
Proof. exact (eq_refl (term405 __1 __0)). Qed.
Lemma lem229964 (__1 : nat) (__0 : nat) : term406 __1 __0.
Proof. exact (EQ_MP (@lem229963 __1 __0) (@lem229962 __1 __0)). Qed.
Lemma lem229965 (__1 : nat) (__0 : nat) : term407 __1 __0.
Proof. exact (@lem229964 __1 __0 (term403 __1 __0)). Qed.
Lemma lem229966 (__1 : nat) (__0 : nat) : (term407 __1 __0) = ((term404 __1 __0) = (term408 __1 __0)).
Proof. exact (eq_refl (term407 __1 __0)). Qed.
Lemma lem229969 (__1 : nat) (__0 : nat) : (term404 __1 __0) = (term408 __1 __0).
Proof. exact (EQ_MP (@lem229966 __1 __0) (@lem229965 __1 __0)). Qed.
Lemma lem229972 (__1 : nat) (__0 : nat) : term408 __1 __0.
Proof. exact (EQ_MP (@lem229969 __1 __0) (@lem229961 __1 __0)). Qed.
Lemma lem229976 (__1 : nat) (__0 : nat) : (term9 __1 __0) = (term9 __1 __0).
Proof. exact (eq_refl (term9 __1 __0)). Qed.
Lemma lem229977 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term409 __1 __0.
Proof. exact (h1). Qed.
Lemma lem229978 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term410 __1 __0.
Proof. exact (@lem16684 (term411 __1 __0) (term403 __1 __0) h1). Qed.
Lemma lem229979 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : (term409 __1 __0) = (term410 __1 __0).
Proof. exact (prop_ext (fun h2 : term409 __1 __0 => @lem229978 __1 __0 h1) (fun h2 : term410 __1 __0 => @lem229977 __1 __0 h1)). Qed.
Lemma lem229980 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term410 __1 __0.
Proof. exact (EQ_MP (@lem229979 __1 __0 h1) (@lem229977 __1 __0 h1)). Qed.
Lemma lem229981 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term412 __1 __0.
Proof. exact (@lem16597 (term411 __1 __0) (term403 __1 __0) h1). Qed.
Lemma lem229982 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : (term409 __1 __0) = (term412 __1 __0).
Proof. exact (prop_ext (fun h2 : term409 __1 __0 => @lem229981 __1 __0 h1) (fun h2 : term412 __1 __0 => @lem229977 __1 __0 h1)). Qed.
Lemma lem229983 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term412 __1 __0.
Proof. exact (EQ_MP (@lem229982 __1 __0 h1) (@lem229977 __1 __0 h1)). Qed.
Lemma lem229984 (__1 : nat) (__0 : nat) (h1 : term410 __1 __0) : term413 __1 __0.
Proof. exact (@lem16684 (term414 __1 __0) ((term9 __1 __0) = (term4 __1 __0)) h1). Qed.
Lemma lem229985 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : (term410 __1 __0) = (term413 __1 __0).
Proof. exact (prop_ext (fun h2 : term410 __1 __0 => @lem229984 __1 __0 h2) (fun h2 : term413 __1 __0 => @lem229980 __1 __0 h1)). Qed.
Lemma lem229986 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term413 __1 __0.
Proof. exact (EQ_MP (@lem229985 __1 __0 h1) (@lem229980 __1 __0 h1)). Qed.
Lemma lem229987 (__1 : nat) (__0 : nat) (h1 : term410 __1 __0) : term415 __1 __0.
Proof. exact (@lem16597 (term414 __1 __0) ((term9 __1 __0) = (term4 __1 __0)) h1). Qed.
Lemma lem229988 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : (term410 __1 __0) = (term415 __1 __0).
Proof. exact (prop_ext (fun h2 : term410 __1 __0 => @lem229987 __1 __0 h2) (fun h2 : term415 __1 __0 => @lem229980 __1 __0 h1)). Qed.
Lemma lem229989 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term415 __1 __0.
Proof. exact (EQ_MP (@lem229988 __1 __0 h1) (@lem229980 __1 __0 h1)). Qed.
Lemma lem229990 (__1 : nat) (__0 : nat) (h1 : term412 __1 __0) (h2 : term413 __1 __0) : term416 __1 __0.
Proof. exact (@lem16799 (term411 __1 __0) ((term9 __1 __0) = (term4 __1 __0)) h1 h2). Qed.
Lemma lem229991 (__1 : nat) (__0 : nat) (h1 : term412 __1 __0) (h2 : term409 __1 __0) : (term413 __1 __0) = (term416 __1 __0).
Proof. exact (prop_ext (fun h3 : term413 __1 __0 => @lem229990 __1 __0 h1 h3) (fun h3 : term416 __1 __0 => @lem229986 __1 __0 h2)). Qed.
Lemma lem229992 (__1 : nat) (__0 : nat) (h1 : term412 __1 __0) (h2 : term409 __1 __0) : term416 __1 __0.
Proof. exact (EQ_MP (@lem229991 __1 __0 h1 h2) (@lem229986 __1 __0 h2)). Qed.
Lemma lem229993 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : (term412 __1 __0) = (term416 __1 __0).
Proof. exact (prop_ext (fun h2 : term412 __1 __0 => @lem229992 __1 __0 h2 h1) (fun h2 : term416 __1 __0 => @lem229983 __1 __0 h1)). Qed.
Lemma lem229994 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term416 __1 __0.
Proof. exact (EQ_MP (@lem229993 __1 __0 h1) (@lem229983 __1 __0 h1)). Qed.
Lemma lem229995 (__1 : nat) (__0 : nat) (h1 : term415 __1 __0) (h2 : term416 __1 __0) : term417 __1 __0.
Proof. exact (@lem16799 (term414 __1 __0) (term418 __1 __0) h1 h2). Qed.
Lemma lem229996 (__1 : nat) (__0 : nat) (h1 : term415 __1 __0) (h2 : term409 __1 __0) : (term416 __1 __0) = (term417 __1 __0).
Proof. exact (prop_ext (fun h3 : term416 __1 __0 => @lem229995 __1 __0 h1 h3) (fun h3 : term417 __1 __0 => @lem229994 __1 __0 h2)). Qed.
Lemma lem229997 (__1 : nat) (__0 : nat) (h1 : term415 __1 __0) (h2 : term409 __1 __0) : term417 __1 __0.
Proof. exact (EQ_MP (@lem229996 __1 __0 h1 h2) (@lem229994 __1 __0 h2)). Qed.
Lemma lem229998 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : (term415 __1 __0) = (term417 __1 __0).
Proof. exact (prop_ext (fun h2 : term415 __1 __0 => @lem229997 __1 __0 h2 h1) (fun h2 : term417 __1 __0 => @lem229989 __1 __0 h1)). Qed.
Lemma lem229999 (__1 : nat) (__0 : nat) (h1 : term409 __1 __0) : term417 __1 __0.
Proof. exact (EQ_MP (@lem229998 __1 __0 h1) (@lem229989 __1 __0 h1)). Qed.
Lemma lem230000 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term417 __1 __0.
Proof. exact (h1). Qed.
Lemma lem230001 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term416 __1 __0.
Proof. exact (@lem16684 (term414 __1 __0) (term418 __1 __0) h1). Qed.
Lemma lem230002 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : (term417 __1 __0) = (term416 __1 __0).
Proof. exact (prop_ext (fun h2 : term417 __1 __0 => @lem230001 __1 __0 h1) (fun h2 : term416 __1 __0 => @lem230000 __1 __0 h1)). Qed.
Lemma lem230003 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term416 __1 __0.
Proof. exact (EQ_MP (@lem230002 __1 __0 h1) (@lem230000 __1 __0 h1)). Qed.
Lemma lem230004 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term415 __1 __0.
Proof. exact (@lem16597 (term414 __1 __0) (term418 __1 __0) h1). Qed.
Lemma lem230005 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : (term417 __1 __0) = (term415 __1 __0).
Proof. exact (prop_ext (fun h2 : term417 __1 __0 => @lem230004 __1 __0 h1) (fun h2 : term415 __1 __0 => @lem230000 __1 __0 h1)). Qed.
Lemma lem230006 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term415 __1 __0.
Proof. exact (EQ_MP (@lem230005 __1 __0 h1) (@lem230000 __1 __0 h1)). Qed.
Lemma lem230007 (__1 : nat) (__0 : nat) (h1 : term416 __1 __0) : term413 __1 __0.
Proof. exact (@lem16684 (term411 __1 __0) ((term9 __1 __0) = (term4 __1 __0)) h1). Qed.
Lemma lem230008 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : (term416 __1 __0) = (term413 __1 __0).
Proof. exact (prop_ext (fun h2 : term416 __1 __0 => @lem230007 __1 __0 h2) (fun h2 : term413 __1 __0 => @lem230003 __1 __0 h1)). Qed.
Lemma lem230009 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term413 __1 __0.
Proof. exact (EQ_MP (@lem230008 __1 __0 h1) (@lem230003 __1 __0 h1)). Qed.
Lemma lem230010 (__1 : nat) (__0 : nat) (h1 : term416 __1 __0) : term412 __1 __0.
Proof. exact (@lem16597 (term411 __1 __0) ((term9 __1 __0) = (term4 __1 __0)) h1). Qed.
Lemma lem230011 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : (term416 __1 __0) = (term412 __1 __0).
Proof. exact (prop_ext (fun h2 : term416 __1 __0 => @lem230010 __1 __0 h2) (fun h2 : term412 __1 __0 => @lem230003 __1 __0 h1)). Qed.
Lemma lem230012 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term412 __1 __0.
Proof. exact (EQ_MP (@lem230011 __1 __0 h1) (@lem230003 __1 __0 h1)). Qed.
Lemma lem230013 (__1 : nat) (__0 : nat) (h1 : term415 __1 __0) (h2 : term413 __1 __0) : term410 __1 __0.
Proof. exact (@lem16799 (term414 __1 __0) ((term9 __1 __0) = (term4 __1 __0)) h1 h2). Qed.
Lemma lem230014 (__1 : nat) (__0 : nat) (h1 : term415 __1 __0) (h2 : term417 __1 __0) : (term413 __1 __0) = (term410 __1 __0).
Proof. exact (prop_ext (fun h3 : term413 __1 __0 => @lem230013 __1 __0 h1 h3) (fun h3 : term410 __1 __0 => @lem230009 __1 __0 h2)). Qed.
Lemma lem230015 (__1 : nat) (__0 : nat) (h1 : term415 __1 __0) (h2 : term417 __1 __0) : term410 __1 __0.
Proof. exact (EQ_MP (@lem230014 __1 __0 h1 h2) (@lem230009 __1 __0 h2)). Qed.
Lemma lem230016 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : (term415 __1 __0) = (term410 __1 __0).
Proof. exact (prop_ext (fun h2 : term415 __1 __0 => @lem230015 __1 __0 h2 h1) (fun h2 : term410 __1 __0 => @lem230006 __1 __0 h1)). Qed.
Lemma lem230017 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term410 __1 __0.
Proof. exact (EQ_MP (@lem230016 __1 __0 h1) (@lem230006 __1 __0 h1)). Qed.
Lemma lem230018 (__1 : nat) (__0 : nat) (h1 : term412 __1 __0) (h2 : term410 __1 __0) : term409 __1 __0.
Proof. exact (@lem16799 (term411 __1 __0) (term403 __1 __0) h1 h2). Qed.
Lemma lem230019 (__1 : nat) (__0 : nat) (h1 : term412 __1 __0) (h2 : term417 __1 __0) : (term410 __1 __0) = (term409 __1 __0).
Proof. exact (prop_ext (fun h3 : term410 __1 __0 => @lem230018 __1 __0 h1 h3) (fun h3 : term409 __1 __0 => @lem230017 __1 __0 h2)). Qed.
Lemma lem230020 (__1 : nat) (__0 : nat) (h1 : term412 __1 __0) (h2 : term417 __1 __0) : term409 __1 __0.
Proof. exact (EQ_MP (@lem230019 __1 __0 h1 h2) (@lem230017 __1 __0 h2)). Qed.
Lemma lem230021 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : (term412 __1 __0) = (term409 __1 __0).
Proof. exact (prop_ext (fun h2 : term412 __1 __0 => @lem230020 __1 __0 h2 h1) (fun h2 : term409 __1 __0 => @lem230012 __1 __0 h1)). Qed.
Lemma lem230022 (__1 : nat) (__0 : nat) (h1 : term417 __1 __0) : term409 __1 __0.
Proof. exact (EQ_MP (@lem230021 __1 __0 h1) (@lem230012 __1 __0 h1)). Qed.
Lemma lem230023 (__1 : nat) (__0 : nat) : term419 __1 __0.
Proof. exact (fun h0 : term417 __1 __0 => @lem230022 __1 __0 h0). Qed.
Lemma lem230024 (__1 : nat) (__0 : nat) : term420 __1 __0.
Proof. exact (fun h0 : term409 __1 __0 => @lem229999 __1 __0 h0). Qed.
Lemma lem230025 (__1 : nat) (__0 : nat) : term421 __1 __0.
Proof. exact (conj (@lem230024 __1 __0) (@lem230023 __1 __0)). Qed.
Lemma lem230026 (__1 : nat) (__0 : nat) : (term421 __1 __0) = ((term409 __1 __0) = (term417 __1 __0)).
Proof. exact (@lem32 (term409 __1 __0) (term417 __1 __0)). Qed.
Lemma lem230027 (__1 : nat) (__0 : nat) : (term409 __1 __0) = (term417 __1 __0).
Proof. exact (EQ_MP (@lem230026 __1 __0) (@lem230025 __1 __0)). Qed.
Lemma lem230028 (__1 : nat) (__0 : nat) (h1 : (term409 __1 __0) = (term417 __1 __0)) : (term408 __1 __0) = (term422 __1 __0).
Proof. exact (@lem16917 (term408 __1 __0) (term422 __1 __0) h1). Qed.
Lemma lem230029 (__1 : nat) (__0 : nat) : ((term409 __1 __0) = (term417 __1 __0)) = ((term408 __1 __0) = (term422 __1 __0)).
Proof. exact (prop_ext (fun h1 : (term409 __1 __0) = (term417 __1 __0) => @lem230028 __1 __0 h1) (fun h1 : (term408 __1 __0) = (term422 __1 __0) => @lem230027 __1 __0)). Qed.
Lemma lem230032 (__1 : nat) (__0 : nat) : (term408 __1 __0) = (term422 __1 __0).
Proof. exact (EQ_MP (@lem230029 __1 __0) (@lem230027 __1 __0)). Qed.
Lemma lem230033 (__1 : nat) (__0 : nat) : term422 __1 __0.
Proof. exact (EQ_MP (@lem230032 __1 __0) (@lem229972 __1 __0)). Qed.
Lemma lem230034 (__1 : nat) (__0 : nat) : term423 __1 __0.
Proof. exact (@lem22025 ((term9 __1 __0) = (term9 __1 __0))). Qed.
Lemma lem230035 (__1 : nat) (__0 : nat) : (term423 __1 __0) = (term424 __1 __0).
Proof. exact (eq_refl (term423 __1 __0)). Qed.
Lemma lem230036 (__1 : nat) (__0 : nat) : term424 __1 __0.
Proof. exact (EQ_MP (@lem230035 __1 __0) (@lem230034 __1 __0)). Qed.
Lemma lem230037 (__1 : nat) (__0 : nat) : term425 __1 __0.
Proof. exact (@lem230036 __1 __0 (term418 __1 __0)). Qed.
Lemma lem230038 (__1 : nat) (__0 : nat) : (term425 __1 __0) = (term426 __1 __0).
Proof. exact (eq_refl (term425 __1 __0)). Qed.
Lemma lem230039 (__1 : nat) (__0 : nat) : term426 __1 __0.
Proof. exact (EQ_MP (@lem230038 __1 __0) (@lem230037 __1 __0)). Qed.
Lemma lem230040 (__1 : nat) (__0 : nat) : term427 __1 __0.
Proof. exact (@lem230039 __1 __0 (@lem229976 __1 __0)). Qed.
Lemma lem230047 (__1 : nat) (__0 : nat) (h1 : term277) : (term396 __1 __0) = (term236 __1 __0).
Proof. exact (@lem229933 __0 (Nat.div __1 __0) h1). Qed.
Lemma lem230051 (__1 : nat) (__0 : nat) : term418 __1 __0.
Proof. exact (@lem230040 __1 __0 (@lem230033 __1 __0)). Qed.
Lemma lem230052 (__1 : nat) (__0 : nat) : term428 __1 __0.
Proof. exact (@lem22025 ((term396 __1 __0) = (term236 __1 __0))). Qed.
Lemma lem230053 (__1 : nat) (__0 : nat) : (term428 __1 __0) = (term429 __1 __0).
Proof. exact (eq_refl (term428 __1 __0)). Qed.
Lemma lem230054 (__1 : nat) (__0 : nat) : term429 __1 __0.
Proof. exact (EQ_MP (@lem230053 __1 __0) (@lem230052 __1 __0)). Qed.
Lemma lem230055 (__1 : nat) (__0 : nat) : term430 __1 __0.
Proof. exact (@lem230054 __1 __0 ((term9 __1 __0) = (term4 __1 __0))). Qed.
Lemma lem230056 (__1 : nat) (__0 : nat) : (term430 __1 __0) = (term431 __1 __0).
Proof. exact (eq_refl (term430 __1 __0)). Qed.
Lemma lem230057 (__1 : nat) (__0 : nat) : term431 __1 __0.
Proof. exact (EQ_MP (@lem230056 __1 __0) (@lem230055 __1 __0)). Qed.
Lemma lem230058 (__1 : nat) (__0 : nat) (h1 : term277) : term432 __1 __0.
Proof. exact (@lem230057 __1 __0 (@lem230047 __1 __0 h1)). Qed.
Lemma lem230063 (__1 : nat) (__0 : nat) (h1 : term239 __1 __0) : term239 __1 __0.
Proof. exact (h1). Qed.
Lemma lem230065 (__1 : nat) (__0 : nat) (h1 : __1 = (term9 __1 __0)) : __1 = (term9 __1 __0).
Proof. exact (h1). Qed.
Lemma lem230066 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem230067 (__1 : nat) (__0 : nat) (h1 : __1 = (term9 __1 __0)) : (@eq nat __1) = (term398 __1 __0).
Proof. exact (MK_COMB (@lem230066) (@lem230065 __1 __0 h1)). Qed.
Lemma lem230068 (__1 : nat) (__0 : nat) : (term4 __1 __0) = (term4 __1 __0).
Proof. exact (eq_refl (term4 __1 __0)). Qed.
Lemma lem230069 (__1 : nat) (__0 : nat) (h1 : __1 = (term9 __1 __0)) : (__1 = (term4 __1 __0)) = ((term9 __1 __0) = (term4 __1 __0)).
Proof. exact (MK_COMB (@lem230067 __1 __0 h1) (@lem230068 __1 __0)). Qed.
Lemma lem230070 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem230071 (__1 : nat) (__0 : nat) (h1 : __1 = (term9 __1 __0)) : (term239 __1 __0) = (term413 __1 __0).
Proof. exact (MK_COMB (@lem230070) (@lem230069 __1 __0 h1)). Qed.
Lemma lem230072 (__1 : nat) (__0 : nat) (h1 : term239 __1 __0) (h2 : __1 = (term9 __1 __0)) : term413 __1 __0.
Proof. exact (EQ_MP (@lem230071 __1 __0 h2) (@lem230063 __1 __0 h1)). Qed.
Lemma lem230073 (__1 : nat) (__0 : nat) (h1 : __1 = (term9 __1 __0)) : term433 __1 __0.
Proof. exact (fun h0 : term239 __1 __0 => @lem230072 __1 __0 h0 h1). Qed.
Lemma lem230074 (__1 : nat) (__0 : nat) : term434 __1 __0.
Proof. exact (@lem22403 (__1 = (term4 __1 __0))). Qed.
Lemma lem230075 (__1 : nat) (__0 : nat) : (term434 __1 __0) = (term435 __1 __0).
Proof. exact (eq_refl (term434 __1 __0)). Qed.
Lemma lem230076 (__1 : nat) (__0 : nat) : term435 __1 __0.
Proof. exact (EQ_MP (@lem230075 __1 __0) (@lem230074 __1 __0)). Qed.
Lemma lem230077 (__1 : nat) (__0 : nat) : term436 __1 __0.
Proof. exact (@lem230076 __1 __0 (term413 __1 __0)). Qed.
Lemma lem230078 (__1 : nat) (__0 : nat) : (term436 __1 __0) = ((term433 __1 __0) = (term437 __1 __0)).
Proof. exact (eq_refl (term436 __1 __0)). Qed.
Lemma lem230081 (__1 : nat) (__0 : nat) : (term433 __1 __0) = (term437 __1 __0).
Proof. exact (EQ_MP (@lem230078 __1 __0) (@lem230077 __1 __0)). Qed.
Lemma lem230082 (__1 : nat) (__0 : nat) (h1 : __1 = (term9 __1 __0)) : term437 __1 __0.
Proof. exact (EQ_MP (@lem230081 __1 __0) (@lem230073 __1 __0 h1)). Qed.
Lemma lem230083 (__1 : nat) (__0 : nat) : term438 __1 __0.
Proof. exact (fun h0 : __1 = (term9 __1 __0) => @lem230082 __1 __0 h0). Qed.
Lemma lem230084 (__1 : nat) (__0 : nat) : term439 __1 __0.
Proof. exact (@lem22518 (__1 = (term9 __1 __0))). Qed.
Lemma lem230085 (__1 : nat) (__0 : nat) : (term439 __1 __0) = (term440 __1 __0).
Proof. exact (eq_refl (term439 __1 __0)). Qed.
Lemma lem230086 (__1 : nat) (__0 : nat) : term440 __1 __0.
Proof. exact (EQ_MP (@lem230085 __1 __0) (@lem230084 __1 __0)). Qed.
Lemma lem230087 (__1 : nat) (__0 : nat) : term441 __1 __0.
Proof. exact (@lem230086 __1 __0 (term437 __1 __0)). Qed.
Lemma lem230088 (__1 : nat) (__0 : nat) : (term441 __1 __0) = ((term438 __1 __0) = (term442 __1 __0)).
Proof. exact (eq_refl (term441 __1 __0)). Qed.
Lemma lem230091 (__1 : nat) (__0 : nat) : (term438 __1 __0) = (term442 __1 __0).
Proof. exact (EQ_MP (@lem230088 __1 __0) (@lem230087 __1 __0)). Qed.
Lemma lem230092 (__1 : nat) (__0 : nat) : term442 __1 __0.
Proof. exact (EQ_MP (@lem230091 __1 __0) (@lem230083 __1 __0)). Qed.
Lemma lem230093 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term443 __1 __0.
Proof. exact (h1). Qed.
Lemma lem230094 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term444 __1 __0.
Proof. exact (@lem16684 (term300 __1 __0) (term437 __1 __0) h1). Qed.
Lemma lem230095 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : (term443 __1 __0) = (term444 __1 __0).
Proof. exact (prop_ext (fun h2 : term443 __1 __0 => @lem230094 __1 __0 h1) (fun h2 : term444 __1 __0 => @lem230093 __1 __0 h1)). Qed.
Lemma lem230096 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term444 __1 __0.
Proof. exact (EQ_MP (@lem230095 __1 __0 h1) (@lem230093 __1 __0 h1)). Qed.
Lemma lem230097 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term445 __1 __0.
Proof. exact (@lem16597 (term300 __1 __0) (term437 __1 __0) h1). Qed.
Lemma lem230098 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : (term443 __1 __0) = (term445 __1 __0).
Proof. exact (prop_ext (fun h2 : term443 __1 __0 => @lem230097 __1 __0 h1) (fun h2 : term445 __1 __0 => @lem230093 __1 __0 h1)). Qed.
Lemma lem230099 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term445 __1 __0.
Proof. exact (EQ_MP (@lem230098 __1 __0 h1) (@lem230093 __1 __0 h1)). Qed.
Lemma lem230100 (__1 : nat) (__0 : nat) (h1 : term444 __1 __0) : term446 __1 __0.
Proof. exact (@lem16684 (__1 = (term4 __1 __0)) (term413 __1 __0) h1). Qed.
Lemma lem230101 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : (term444 __1 __0) = (term446 __1 __0).
Proof. exact (prop_ext (fun h2 : term444 __1 __0 => @lem230100 __1 __0 h2) (fun h2 : term446 __1 __0 => @lem230096 __1 __0 h1)). Qed.
Lemma lem230102 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term446 __1 __0.
Proof. exact (EQ_MP (@lem230101 __1 __0 h1) (@lem230096 __1 __0 h1)). Qed.
Lemma lem230103 (__1 : nat) (__0 : nat) (h1 : term444 __1 __0) : term239 __1 __0.
Proof. exact (@lem16597 (__1 = (term4 __1 __0)) (term413 __1 __0) h1). Qed.
Lemma lem230104 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : (term444 __1 __0) = (term239 __1 __0).
Proof. exact (prop_ext (fun h2 : term444 __1 __0 => @lem230103 __1 __0 h2) (fun h2 : term239 __1 __0 => @lem230096 __1 __0 h1)). Qed.
Lemma lem230105 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term239 __1 __0.
Proof. exact (EQ_MP (@lem230104 __1 __0 h1) (@lem230096 __1 __0 h1)). Qed.
Lemma lem230106 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term239 __1 __0) : term447 __1 __0.
Proof. exact (@lem16799 (term413 __1 __0) (__1 = (term4 __1 __0)) h1 h2). Qed.
Lemma lem230107 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term443 __1 __0) : (term239 __1 __0) = (term447 __1 __0).
Proof. exact (prop_ext (fun h3 : term239 __1 __0 => @lem230106 __1 __0 h1 h3) (fun h3 : term447 __1 __0 => @lem230105 __1 __0 h2)). Qed.
Lemma lem230108 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term443 __1 __0) : term447 __1 __0.
Proof. exact (EQ_MP (@lem230107 __1 __0 h1 h2) (@lem230105 __1 __0 h2)). Qed.
Lemma lem230109 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : (term446 __1 __0) = (term447 __1 __0).
Proof. exact (prop_ext (fun h2 : term446 __1 __0 => @lem230108 __1 __0 h2 h1) (fun h2 : term447 __1 __0 => @lem230102 __1 __0 h1)). Qed.
Lemma lem230110 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term447 __1 __0.
Proof. exact (EQ_MP (@lem230109 __1 __0 h1) (@lem230102 __1 __0 h1)). Qed.
Lemma lem230111 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term447 __1 __0) : term448 __1 __0.
Proof. exact (@lem16799 (term300 __1 __0) (term449 __1 __0) h1 h2). Qed.
Lemma lem230112 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term443 __1 __0) : (term447 __1 __0) = (term448 __1 __0).
Proof. exact (prop_ext (fun h3 : term447 __1 __0 => @lem230111 __1 __0 h1 h3) (fun h3 : term448 __1 __0 => @lem230110 __1 __0 h2)). Qed.
Lemma lem230113 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term443 __1 __0) : term448 __1 __0.
Proof. exact (EQ_MP (@lem230112 __1 __0 h1 h2) (@lem230110 __1 __0 h2)). Qed.
Lemma lem230114 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : (term445 __1 __0) = (term448 __1 __0).
Proof. exact (prop_ext (fun h2 : term445 __1 __0 => @lem230113 __1 __0 h2 h1) (fun h2 : term448 __1 __0 => @lem230099 __1 __0 h1)). Qed.
Lemma lem230115 (__1 : nat) (__0 : nat) (h1 : term443 __1 __0) : term448 __1 __0.
Proof. exact (EQ_MP (@lem230114 __1 __0 h1) (@lem230099 __1 __0 h1)). Qed.
Lemma lem230116 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term448 __1 __0.
Proof. exact (h1). Qed.
Lemma lem230117 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term447 __1 __0.
Proof. exact (@lem16684 (term300 __1 __0) (term449 __1 __0) h1). Qed.
Lemma lem230118 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term448 __1 __0) = (term447 __1 __0).
Proof. exact (prop_ext (fun h2 : term448 __1 __0 => @lem230117 __1 __0 h1) (fun h2 : term447 __1 __0 => @lem230116 __1 __0 h1)). Qed.
Lemma lem230119 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term447 __1 __0.
Proof. exact (EQ_MP (@lem230118 __1 __0 h1) (@lem230116 __1 __0 h1)). Qed.
Lemma lem230120 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term445 __1 __0.
Proof. exact (@lem16597 (term300 __1 __0) (term449 __1 __0) h1). Qed.
Lemma lem230121 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term448 __1 __0) = (term445 __1 __0).
Proof. exact (prop_ext (fun h2 : term448 __1 __0 => @lem230120 __1 __0 h1) (fun h2 : term445 __1 __0 => @lem230116 __1 __0 h1)). Qed.
Lemma lem230122 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term445 __1 __0.
Proof. exact (EQ_MP (@lem230121 __1 __0 h1) (@lem230116 __1 __0 h1)). Qed.
Lemma lem230123 (__1 : nat) (__0 : nat) (h1 : term447 __1 __0) : term239 __1 __0.
Proof. exact (@lem16684 (term413 __1 __0) (__1 = (term4 __1 __0)) h1). Qed.
Lemma lem230124 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term447 __1 __0) = (term239 __1 __0).
Proof. exact (prop_ext (fun h2 : term447 __1 __0 => @lem230123 __1 __0 h2) (fun h2 : term239 __1 __0 => @lem230119 __1 __0 h1)). Qed.
Lemma lem230125 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term239 __1 __0.
Proof. exact (EQ_MP (@lem230124 __1 __0 h1) (@lem230119 __1 __0 h1)). Qed.
Lemma lem230126 (__1 : nat) (__0 : nat) (h1 : term447 __1 __0) : term446 __1 __0.
Proof. exact (@lem16597 (term413 __1 __0) (__1 = (term4 __1 __0)) h1). Qed.
Lemma lem230127 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term447 __1 __0) = (term446 __1 __0).
Proof. exact (prop_ext (fun h2 : term447 __1 __0 => @lem230126 __1 __0 h2) (fun h2 : term446 __1 __0 => @lem230119 __1 __0 h1)). Qed.
Lemma lem230128 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term446 __1 __0.
Proof. exact (EQ_MP (@lem230127 __1 __0 h1) (@lem230119 __1 __0 h1)). Qed.
Lemma lem230129 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term239 __1 __0) : term444 __1 __0.
Proof. exact (@lem16799 (__1 = (term4 __1 __0)) (term413 __1 __0) h2 h1). Qed.
Lemma lem230130 (__1 : nat) (__0 : nat) (h1 : term239 __1 __0) (h2 : term448 __1 __0) : (term446 __1 __0) = (term444 __1 __0).
Proof. exact (prop_ext (fun h3 : term446 __1 __0 => @lem230129 __1 __0 h3 h1) (fun h3 : term444 __1 __0 => @lem230128 __1 __0 h2)). Qed.
Lemma lem230131 (__1 : nat) (__0 : nat) (h1 : term239 __1 __0) (h2 : term448 __1 __0) : term444 __1 __0.
Proof. exact (EQ_MP (@lem230130 __1 __0 h1 h2) (@lem230128 __1 __0 h2)). Qed.
Lemma lem230132 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term239 __1 __0) = (term444 __1 __0).
Proof. exact (prop_ext (fun h2 : term239 __1 __0 => @lem230131 __1 __0 h2 h1) (fun h2 : term444 __1 __0 => @lem230125 __1 __0 h1)). Qed.
Lemma lem230133 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term444 __1 __0.
Proof. exact (EQ_MP (@lem230132 __1 __0 h1) (@lem230125 __1 __0 h1)). Qed.
Lemma lem230134 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term444 __1 __0) : term443 __1 __0.
Proof. exact (@lem16799 (term300 __1 __0) (term437 __1 __0) h1 h2). Qed.
Lemma lem230135 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term448 __1 __0) : (term444 __1 __0) = (term443 __1 __0).
Proof. exact (prop_ext (fun h3 : term444 __1 __0 => @lem230134 __1 __0 h1 h3) (fun h3 : term443 __1 __0 => @lem230133 __1 __0 h2)). Qed.
Lemma lem230136 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term448 __1 __0) : term443 __1 __0.
Proof. exact (EQ_MP (@lem230135 __1 __0 h1 h2) (@lem230133 __1 __0 h2)). Qed.
Lemma lem230137 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term445 __1 __0) = (term443 __1 __0).
Proof. exact (prop_ext (fun h2 : term445 __1 __0 => @lem230136 __1 __0 h2 h1) (fun h2 : term443 __1 __0 => @lem230122 __1 __0 h1)). Qed.
Lemma lem230138 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term443 __1 __0.
Proof. exact (EQ_MP (@lem230137 __1 __0 h1) (@lem230122 __1 __0 h1)). Qed.
Lemma lem230139 (__1 : nat) (__0 : nat) : term450 __1 __0.
Proof. exact (fun h0 : term448 __1 __0 => @lem230138 __1 __0 h0). Qed.
Lemma lem230140 (__1 : nat) (__0 : nat) : term451 __1 __0.
Proof. exact (fun h0 : term443 __1 __0 => @lem230115 __1 __0 h0). Qed.
Lemma lem230141 (__1 : nat) (__0 : nat) : term452 __1 __0.
Proof. exact (conj (@lem230140 __1 __0) (@lem230139 __1 __0)). Qed.
Lemma lem230142 (__1 : nat) (__0 : nat) : (term452 __1 __0) = ((term443 __1 __0) = (term448 __1 __0)).
Proof. exact (@lem32 (term443 __1 __0) (term448 __1 __0)). Qed.
Lemma lem230143 (__1 : nat) (__0 : nat) : (term443 __1 __0) = (term448 __1 __0).
Proof. exact (EQ_MP (@lem230142 __1 __0) (@lem230141 __1 __0)). Qed.
Lemma lem230144 (__1 : nat) (__0 : nat) (h1 : (term443 __1 __0) = (term448 __1 __0)) : (term442 __1 __0) = (term453 __1 __0).
Proof. exact (@lem16917 (term442 __1 __0) (term453 __1 __0) h1). Qed.
Lemma lem230145 (__1 : nat) (__0 : nat) : ((term443 __1 __0) = (term448 __1 __0)) = ((term442 __1 __0) = (term453 __1 __0)).
Proof. exact (prop_ext (fun h1 : (term443 __1 __0) = (term448 __1 __0) => @lem230144 __1 __0 h1) (fun h1 : (term442 __1 __0) = (term453 __1 __0) => @lem230143 __1 __0)). Qed.
Lemma lem230146 (__1 : nat) (__0 : nat) : (term442 __1 __0) = (term453 __1 __0).
Proof. exact (EQ_MP (@lem230145 __1 __0) (@lem230143 __1 __0)). Qed.
Lemma lem230147 (__1 : nat) (__0 : nat) : term453 __1 __0.
Proof. exact (EQ_MP (@lem230146 __1 __0) (@lem230092 __1 __0)). Qed.
Lemma lem230151 (__1 : nat) (__0 : nat) (h1 : term277) : (term9 __1 __0) = (term4 __1 __0).
Proof. exact (@lem230058 __1 __0 h1 (@lem230051 __1 __0)). Qed.
Lemma lem230152 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term448 __1 __0.
Proof. exact (h1). Qed.
Lemma lem230153 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term447 __1 __0.
Proof. exact (@lem16684 (term300 __1 __0) (term449 __1 __0) h1). Qed.
Lemma lem230154 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term448 __1 __0) = (term447 __1 __0).
Proof. exact (prop_ext (fun h2 : term448 __1 __0 => @lem230153 __1 __0 h1) (fun h2 : term447 __1 __0 => @lem230152 __1 __0 h1)). Qed.
Lemma lem230155 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term447 __1 __0.
Proof. exact (EQ_MP (@lem230154 __1 __0 h1) (@lem230152 __1 __0 h1)). Qed.
Lemma lem230156 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term445 __1 __0.
Proof. exact (@lem16597 (term300 __1 __0) (term449 __1 __0) h1). Qed.
Lemma lem230157 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term448 __1 __0) = (term445 __1 __0).
Proof. exact (prop_ext (fun h2 : term448 __1 __0 => @lem230156 __1 __0 h1) (fun h2 : term445 __1 __0 => @lem230152 __1 __0 h1)). Qed.
Lemma lem230158 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term445 __1 __0.
Proof. exact (EQ_MP (@lem230157 __1 __0 h1) (@lem230152 __1 __0 h1)). Qed.
Lemma lem230159 (__1 : nat) (__0 : nat) (h1 : term447 __1 __0) : term239 __1 __0.
Proof. exact (@lem16684 (term413 __1 __0) (__1 = (term4 __1 __0)) h1). Qed.
Lemma lem230160 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term447 __1 __0) = (term239 __1 __0).
Proof. exact (prop_ext (fun h2 : term447 __1 __0 => @lem230159 __1 __0 h2) (fun h2 : term239 __1 __0 => @lem230155 __1 __0 h1)). Qed.
Lemma lem230161 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term239 __1 __0.
Proof. exact (EQ_MP (@lem230160 __1 __0 h1) (@lem230155 __1 __0 h1)). Qed.
Lemma lem230162 (__1 : nat) (__0 : nat) (h1 : term447 __1 __0) : term446 __1 __0.
Proof. exact (@lem16597 (term413 __1 __0) (__1 = (term4 __1 __0)) h1). Qed.
Lemma lem230163 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term447 __1 __0) = (term446 __1 __0).
Proof. exact (prop_ext (fun h2 : term447 __1 __0 => @lem230162 __1 __0 h2) (fun h2 : term446 __1 __0 => @lem230155 __1 __0 h1)). Qed.
Lemma lem230164 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term446 __1 __0.
Proof. exact (EQ_MP (@lem230163 __1 __0 h1) (@lem230155 __1 __0 h1)). Qed.
Lemma lem230165 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term239 __1 __0) : term454 __1 __0.
Proof. exact (@lem16799 (term300 __1 __0) (__1 = (term4 __1 __0)) h1 h2). Qed.
Lemma lem230166 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term448 __1 __0) : (term239 __1 __0) = (term454 __1 __0).
Proof. exact (prop_ext (fun h3 : term239 __1 __0 => @lem230165 __1 __0 h1 h3) (fun h3 : term454 __1 __0 => @lem230161 __1 __0 h2)). Qed.
Lemma lem230167 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term448 __1 __0) : term454 __1 __0.
Proof. exact (EQ_MP (@lem230166 __1 __0 h1 h2) (@lem230161 __1 __0 h2)). Qed.
Lemma lem230168 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term445 __1 __0) = (term454 __1 __0).
Proof. exact (prop_ext (fun h2 : term445 __1 __0 => @lem230167 __1 __0 h2 h1) (fun h2 : term454 __1 __0 => @lem230158 __1 __0 h1)). Qed.
Lemma lem230169 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term454 __1 __0.
Proof. exact (EQ_MP (@lem230168 __1 __0 h1) (@lem230158 __1 __0 h1)). Qed.
Lemma lem230170 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term454 __1 __0) : term455 __1 __0.
Proof. exact (@lem16799 (term413 __1 __0) (term456 __1 __0) h1 h2). Qed.
Lemma lem230171 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term448 __1 __0) : (term454 __1 __0) = (term455 __1 __0).
Proof. exact (prop_ext (fun h3 : term454 __1 __0 => @lem230170 __1 __0 h1 h3) (fun h3 : term455 __1 __0 => @lem230169 __1 __0 h2)). Qed.
Lemma lem230172 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term448 __1 __0) : term455 __1 __0.
Proof. exact (EQ_MP (@lem230171 __1 __0 h1 h2) (@lem230169 __1 __0 h2)). Qed.
Lemma lem230173 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : (term446 __1 __0) = (term455 __1 __0).
Proof. exact (prop_ext (fun h2 : term446 __1 __0 => @lem230172 __1 __0 h2 h1) (fun h2 : term455 __1 __0 => @lem230164 __1 __0 h1)). Qed.
Lemma lem230174 (__1 : nat) (__0 : nat) (h1 : term448 __1 __0) : term455 __1 __0.
Proof. exact (EQ_MP (@lem230173 __1 __0 h1) (@lem230164 __1 __0 h1)). Qed.
Lemma lem230175 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term455 __1 __0.
Proof. exact (h1). Qed.
Lemma lem230176 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term454 __1 __0.
Proof. exact (@lem16684 (term413 __1 __0) (term456 __1 __0) h1). Qed.
Lemma lem230177 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : (term455 __1 __0) = (term454 __1 __0).
Proof. exact (prop_ext (fun h2 : term455 __1 __0 => @lem230176 __1 __0 h1) (fun h2 : term454 __1 __0 => @lem230175 __1 __0 h1)). Qed.
Lemma lem230178 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term454 __1 __0.
Proof. exact (EQ_MP (@lem230177 __1 __0 h1) (@lem230175 __1 __0 h1)). Qed.
Lemma lem230179 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term446 __1 __0.
Proof. exact (@lem16597 (term413 __1 __0) (term456 __1 __0) h1). Qed.
Lemma lem230180 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : (term455 __1 __0) = (term446 __1 __0).
Proof. exact (prop_ext (fun h2 : term455 __1 __0 => @lem230179 __1 __0 h1) (fun h2 : term446 __1 __0 => @lem230175 __1 __0 h1)). Qed.
Lemma lem230181 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term446 __1 __0.
Proof. exact (EQ_MP (@lem230180 __1 __0 h1) (@lem230175 __1 __0 h1)). Qed.
Lemma lem230182 (__1 : nat) (__0 : nat) (h1 : term454 __1 __0) : term239 __1 __0.
Proof. exact (@lem16684 (term300 __1 __0) (__1 = (term4 __1 __0)) h1). Qed.
Lemma lem230183 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : (term454 __1 __0) = (term239 __1 __0).
Proof. exact (prop_ext (fun h2 : term454 __1 __0 => @lem230182 __1 __0 h2) (fun h2 : term239 __1 __0 => @lem230178 __1 __0 h1)). Qed.
Lemma lem230184 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term239 __1 __0.
Proof. exact (EQ_MP (@lem230183 __1 __0 h1) (@lem230178 __1 __0 h1)). Qed.
Lemma lem230185 (__1 : nat) (__0 : nat) (h1 : term454 __1 __0) : term445 __1 __0.
Proof. exact (@lem16597 (term300 __1 __0) (__1 = (term4 __1 __0)) h1). Qed.
Lemma lem230186 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : (term454 __1 __0) = (term445 __1 __0).
Proof. exact (prop_ext (fun h2 : term454 __1 __0 => @lem230185 __1 __0 h2) (fun h2 : term445 __1 __0 => @lem230178 __1 __0 h1)). Qed.
Lemma lem230187 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term445 __1 __0.
Proof. exact (EQ_MP (@lem230186 __1 __0 h1) (@lem230178 __1 __0 h1)). Qed.
Lemma lem230188 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term239 __1 __0) : term447 __1 __0.
Proof. exact (@lem16799 (term413 __1 __0) (__1 = (term4 __1 __0)) h1 h2). Qed.
Lemma lem230189 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term455 __1 __0) : (term239 __1 __0) = (term447 __1 __0).
Proof. exact (prop_ext (fun h3 : term239 __1 __0 => @lem230188 __1 __0 h1 h3) (fun h3 : term447 __1 __0 => @lem230184 __1 __0 h2)). Qed.
Lemma lem230190 (__1 : nat) (__0 : nat) (h1 : term446 __1 __0) (h2 : term455 __1 __0) : term447 __1 __0.
Proof. exact (EQ_MP (@lem230189 __1 __0 h1 h2) (@lem230184 __1 __0 h2)). Qed.
Lemma lem230191 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : (term446 __1 __0) = (term447 __1 __0).
Proof. exact (prop_ext (fun h2 : term446 __1 __0 => @lem230190 __1 __0 h2 h1) (fun h2 : term447 __1 __0 => @lem230181 __1 __0 h1)). Qed.
Lemma lem230192 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term447 __1 __0.
Proof. exact (EQ_MP (@lem230191 __1 __0 h1) (@lem230181 __1 __0 h1)). Qed.
Lemma lem230193 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term447 __1 __0) : term448 __1 __0.
Proof. exact (@lem16799 (term300 __1 __0) (term449 __1 __0) h1 h2). Qed.
Lemma lem230194 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term455 __1 __0) : (term447 __1 __0) = (term448 __1 __0).
Proof. exact (prop_ext (fun h3 : term447 __1 __0 => @lem230193 __1 __0 h1 h3) (fun h3 : term448 __1 __0 => @lem230192 __1 __0 h2)). Qed.
Lemma lem230195 (__1 : nat) (__0 : nat) (h1 : term445 __1 __0) (h2 : term455 __1 __0) : term448 __1 __0.
Proof. exact (EQ_MP (@lem230194 __1 __0 h1 h2) (@lem230192 __1 __0 h2)). Qed.
Lemma lem230196 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : (term445 __1 __0) = (term448 __1 __0).
Proof. exact (prop_ext (fun h2 : term445 __1 __0 => @lem230195 __1 __0 h2 h1) (fun h2 : term448 __1 __0 => @lem230187 __1 __0 h1)). Qed.
Lemma lem230197 (__1 : nat) (__0 : nat) (h1 : term455 __1 __0) : term448 __1 __0.
Proof. exact (EQ_MP (@lem230196 __1 __0 h1) (@lem230187 __1 __0 h1)). Qed.
Lemma lem230198 (__1 : nat) (__0 : nat) : term457 __1 __0.
Proof. exact (fun h0 : term455 __1 __0 => @lem230197 __1 __0 h0). Qed.
Lemma lem230199 (__1 : nat) (__0 : nat) : term458 __1 __0.
Proof. exact (fun h0 : term448 __1 __0 => @lem230174 __1 __0 h0). Qed.
Lemma lem230200 (__1 : nat) (__0 : nat) : term459 __1 __0.
Proof. exact (conj (@lem230199 __1 __0) (@lem230198 __1 __0)). Qed.
Lemma lem230201 (__1 : nat) (__0 : nat) : (term459 __1 __0) = ((term448 __1 __0) = (term455 __1 __0)).
Proof. exact (@lem32 (term448 __1 __0) (term455 __1 __0)). Qed.
Lemma lem230202 (__1 : nat) (__0 : nat) : (term448 __1 __0) = (term455 __1 __0).
Proof. exact (EQ_MP (@lem230201 __1 __0) (@lem230200 __1 __0)). Qed.
Lemma lem230203 (__1 : nat) (__0 : nat) (h1 : (term448 __1 __0) = (term455 __1 __0)) : (term453 __1 __0) = (term460 __1 __0).
Proof. exact (@lem16917 (term453 __1 __0) (term460 __1 __0) h1). Qed.
Lemma lem230204 (__1 : nat) (__0 : nat) : ((term448 __1 __0) = (term455 __1 __0)) = ((term453 __1 __0) = (term460 __1 __0)).
Proof. exact (prop_ext (fun h1 : (term448 __1 __0) = (term455 __1 __0) => @lem230203 __1 __0 h1) (fun h1 : (term453 __1 __0) = (term460 __1 __0) => @lem230202 __1 __0)). Qed.
Lemma lem230207 (__1 : nat) (__0 : nat) : (term453 __1 __0) = (term460 __1 __0).
Proof. exact (EQ_MP (@lem230204 __1 __0) (@lem230202 __1 __0)). Qed.
Lemma lem230208 (__1 : nat) (__0 : nat) : term460 __1 __0.
Proof. exact (EQ_MP (@lem230207 __1 __0) (@lem230147 __1 __0)). Qed.
Lemma lem230209 (__1 : nat) (__0 : nat) : term461 __1 __0.
Proof. exact (@lem22025 ((term9 __1 __0) = (term4 __1 __0))). Qed.
Lemma lem230210 (__1 : nat) (__0 : nat) : (term461 __1 __0) = (term462 __1 __0).
Proof. exact (eq_refl (term461 __1 __0)). Qed.
Lemma lem230211 (__1 : nat) (__0 : nat) : term462 __1 __0.
Proof. exact (EQ_MP (@lem230210 __1 __0) (@lem230209 __1 __0)). Qed.
Lemma lem230212 (__1 : nat) (__0 : nat) : term463 __1 __0.
Proof. exact (@lem230211 __1 __0 (term456 __1 __0)). Qed.
Lemma lem230213 (__1 : nat) (__0 : nat) : (term463 __1 __0) = (term464 __1 __0).
Proof. exact (eq_refl (term463 __1 __0)). Qed.
Lemma lem230214 (__1 : nat) (__0 : nat) : term464 __1 __0.
Proof. exact (EQ_MP (@lem230213 __1 __0) (@lem230212 __1 __0)). Qed.
Lemma lem230215 (__1 : nat) (__0 : nat) (h1 : term277) : term465 __1 __0.
Proof. exact (@lem230214 __1 __0 (@lem230151 __1 __0 h1)). Qed.
Lemma lem230219 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term385 p __1 __0.
Proof. exact (h1). Qed.
Lemma lem230220 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term300 __1 __0.
Proof. exact (@lem16684 (__0 = p) (__1 = (term9 __1 __0)) h1). Qed.
Lemma lem230221 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : (term385 p __1 __0) = (term300 __1 __0).
Proof. exact (prop_ext (fun h2 : term385 p __1 __0 => @lem230220 p __1 __0 h1) (fun h2 : term300 __1 __0 => @lem230219 p __1 __0 h1)). Qed.
Lemma lem230222 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term300 __1 __0.
Proof. exact (EQ_MP (@lem230221 p __1 __0 h1) (@lem230219 p __1 __0 h1)). Qed.
Lemma lem230223 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term87 __0 p.
Proof. exact (@lem16597 (__0 = p) (__1 = (term9 __1 __0)) h1). Qed.
Lemma lem230224 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : (term385 p __1 __0) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term385 p __1 __0 => @lem230223 p __1 __0 h1) (fun h2 : term87 __0 p => @lem230219 p __1 __0 h1)). Qed.
Lemma lem230225 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term87 __0 p.
Proof. exact (EQ_MP (@lem230224 p __1 __0 h1) (@lem230219 p __1 __0 h1)). Qed.
Lemma lem230226 (p : nat) (__1 : nat) (__0 : nat) (h1 : term87 __0 p) (h2 : term300 __1 __0) : term384 __1 __0 p.
Proof. exact (@lem16799 (__1 = (term9 __1 __0)) (__0 = p) h2 h1). Qed.
Lemma lem230227 (p : nat) (__1 : nat) (__0 : nat) (h1 : term300 __1 __0) (h2 : term385 p __1 __0) : (term87 __0 p) = (term384 __1 __0 p).
Proof. exact (prop_ext (fun h3 : term87 __0 p => @lem230226 p __1 __0 h3 h1) (fun h3 : term384 __1 __0 p => @lem230225 p __1 __0 h2)). Qed.
Lemma lem230228 (p : nat) (__1 : nat) (__0 : nat) (h1 : term300 __1 __0) (h2 : term385 p __1 __0) : term384 __1 __0 p.
Proof. exact (EQ_MP (@lem230227 p __1 __0 h1 h2) (@lem230225 p __1 __0 h2)). Qed.
Lemma lem230229 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : (term300 __1 __0) = (term384 __1 __0 p).
Proof. exact (prop_ext (fun h2 : term300 __1 __0 => @lem230228 p __1 __0 h2 h1) (fun h2 : term384 __1 __0 p => @lem230222 p __1 __0 h1)). Qed.
Lemma lem230230 (p : nat) (__1 : nat) (__0 : nat) (h1 : term385 p __1 __0) : term384 __1 __0 p.
Proof. exact (EQ_MP (@lem230229 p __1 __0 h1) (@lem230222 p __1 __0 h1)). Qed.
Lemma lem230231 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term384 __1 __0 p.
Proof. exact (h1). Qed.
Lemma lem230232 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term87 __0 p.
Proof. exact (@lem16684 (__1 = (term9 __1 __0)) (__0 = p) h1). Qed.
Lemma lem230233 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : (term384 __1 __0 p) = (term87 __0 p).
Proof. exact (prop_ext (fun h2 : term384 __1 __0 p => @lem230232 __1 __0 p h1) (fun h2 : term87 __0 p => @lem230231 __1 __0 p h1)). Qed.
Lemma lem230234 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term87 __0 p.
Proof. exact (EQ_MP (@lem230233 __1 __0 p h1) (@lem230231 __1 __0 p h1)). Qed.
Lemma lem230235 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term300 __1 __0.
Proof. exact (@lem16597 (__1 = (term9 __1 __0)) (__0 = p) h1). Qed.
Lemma lem230236 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : (term384 __1 __0 p) = (term300 __1 __0).
Proof. exact (prop_ext (fun h2 : term384 __1 __0 p => @lem230235 __1 __0 p h1) (fun h2 : term300 __1 __0 => @lem230231 __1 __0 p h1)). Qed.
Lemma lem230237 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term300 __1 __0.
Proof. exact (EQ_MP (@lem230236 __1 __0 p h1) (@lem230231 __1 __0 p h1)). Qed.
Lemma lem230238 (p : nat) (__1 : nat) (__0 : nat) (h1 : term87 __0 p) (h2 : term300 __1 __0) : term385 p __1 __0.
Proof. exact (@lem16799 (__0 = p) (__1 = (term9 __1 __0)) h1 h2). Qed.
Lemma lem230239 (__1 : nat) (__0 : nat) (p : nat) (h1 : term87 __0 p) (h2 : term384 __1 __0 p) : (term300 __1 __0) = (term385 p __1 __0).
Proof. exact (prop_ext (fun h3 : term300 __1 __0 => @lem230238 p __1 __0 h1 h3) (fun h3 : term385 p __1 __0 => @lem230237 __1 __0 p h2)). Qed.
Lemma lem230240 (__1 : nat) (__0 : nat) (p : nat) (h1 : term87 __0 p) (h2 : term384 __1 __0 p) : term385 p __1 __0.
Proof. exact (EQ_MP (@lem230239 __1 __0 p h1 h2) (@lem230237 __1 __0 p h2)). Qed.
Lemma lem230241 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : (term87 __0 p) = (term385 p __1 __0).
Proof. exact (prop_ext (fun h2 : term87 __0 p => @lem230240 __1 __0 p h2 h1) (fun h2 : term385 p __1 __0 => @lem230234 __1 __0 p h1)). Qed.
Lemma lem230242 (__1 : nat) (__0 : nat) (p : nat) (h1 : term384 __1 __0 p) : term385 p __1 __0.
Proof. exact (EQ_MP (@lem230241 __1 __0 p h1) (@lem230234 __1 __0 p h1)). Qed.
Lemma lem230243 (p : nat) (__1 : nat) (__0 : nat) : term387 p __1 __0.
Proof. exact (fun h0 : term384 __1 __0 p => @lem230242 __1 __0 p h0). Qed.
Lemma lem230244 (__1 : nat) (__0 : nat) (p : nat) : term386 __1 __0 p.
Proof. exact (fun h0 : term385 p __1 __0 => @lem230230 p __1 __0 h0). Qed.
Lemma lem230245 (p : nat) (__1 : nat) (__0 : nat) : term466 p __1 __0.
Proof. exact (conj (@lem230244 __1 __0 p) (@lem230243 p __1 __0)). Qed.
Lemma lem230246 (__1 : nat) (__0 : nat) (p : nat) : (term466 p __1 __0) = ((term385 p __1 __0) = (term384 __1 __0 p)).
Proof. exact (@lem32 (term385 p __1 __0) (term384 __1 __0 p)). Qed.
Lemma lem230247 (__1 : nat) (__0 : nat) (p : nat) : (term385 p __1 __0) = (term384 __1 __0 p).
Proof. exact (EQ_MP (@lem230246 __1 __0 p) (@lem230245 p __1 __0)). Qed.
Lemma lem230248 (__1 : nat) (__0 : nat) (p : nat) (h1 : (term385 p __1 __0) = (term384 __1 __0 p)) : (term389 p __1 __0) = (term383 __1 __0 p).
Proof. exact (@lem16917 (term389 p __1 __0) (term383 __1 __0 p) h1). Qed.
Lemma lem230249 (__1 : nat) (__0 : nat) (p : nat) : ((term385 p __1 __0) = (term384 __1 __0 p)) = ((term389 p __1 __0) = (term383 __1 __0 p)).
Proof. exact (prop_ext (fun h1 : (term385 p __1 __0) = (term384 __1 __0 p) => @lem230248 __1 __0 p h1) (fun h1 : (term389 p __1 __0) = (term383 __1 __0 p) => @lem230247 __1 __0 p)). Qed.
Lemma lem230252 (__1 : nat) (__0 : nat) (p : nat) : (term389 p __1 __0) = (term383 __1 __0 p).
Proof. exact (EQ_MP (@lem230249 __1 __0 p) (@lem230247 __1 __0 p)). Qed.
Lemma lem230253 (__1 : nat) (__0 : nat) (p : nat) (h1 : term246) (h2 : p = (NUMERAL 0)) : term383 __1 __0 p.
Proof. exact (EQ_MP (@lem230252 __1 __0 p) (@lem229797 __1 __0 p h1 h2)). Qed.
Lemma lem230257 (__1 : nat) (__0 : nat) (h1 : term277) : term456 __1 __0.
Proof. exact (@lem230215 __1 __0 h1 (@lem230208 __1 __0)). Qed.
Lemma lem230258 (__1 : nat) (__0 : nat) : term467 __1 __0.
Proof. exact (@lem22288 (__1 = (term9 __1 __0))). Qed.
Lemma lem230259 (__1 : nat) (__0 : nat) : (term467 __1 __0) = (term468 __1 __0).
Proof. exact (eq_refl (term467 __1 __0)). Qed.
Lemma lem230260 (__1 : nat) (__0 : nat) : term468 __1 __0.
Proof. exact (EQ_MP (@lem230259 __1 __0) (@lem230258 __1 __0)). Qed.
Lemma lem230261 (__1 : nat) (__0 : nat) (p : nat) : term469 __1 __0 p.
Proof. exact (@lem230260 __1 __0 (__0 = p)). Qed.
Lemma lem230262 (__1 : nat) (__0 : nat) (p : nat) : (term469 __1 __0 p) = (term470 __1 __0 p).
Proof. exact (eq_refl (term469 __1 __0 p)). Qed.
Lemma lem230263 (__1 : nat) (__0 : nat) (p : nat) : term470 __1 __0 p.
Proof. exact (EQ_MP (@lem230262 __1 __0 p) (@lem230261 __1 __0 p)). Qed.
Lemma lem230264 (p : nat) (__1 : nat) (__0 : nat) : term471 p __1 __0.
Proof. exact (@lem230263 __1 __0 p (__1 = (term4 __1 __0))). Qed.
Lemma lem230265 (p : nat) (__1 : nat) (__0 : nat) : (term471 p __1 __0) = (term472 p __1 __0).
Proof. exact (eq_refl (term471 p __1 __0)). Qed.
Lemma lem230266 (p : nat) (__1 : nat) (__0 : nat) : term472 p __1 __0.
Proof. exact (EQ_MP (@lem230265 p __1 __0) (@lem230264 p __1 __0)). Qed.
Lemma lem230267 (__1 : nat) (__0 : nat) (p : nat) (h1 : term246) (h2 : p = (NUMERAL 0)) : term473 p __1 __0.
Proof. exact (@lem230266 p __1 __0 (@lem230253 __1 __0 p h1 h2)). Qed.
Lemma lem230270 (__1 : nat) (__0 : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term474 p __1 __0.
Proof. exact (@lem230267 __1 __0 p h2 h3 (@lem230257 __1 __0 h1)). Qed.
Lemma lem230271 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term474 p m n.
Proof. exact (@lem230270 m n p h1 h2 h3). Qed.
Lemma lem230272 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : term475 p m n.
Proof. exact (h1). Qed.
Lemma lem230273 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : term239 m n.
Proof. exact (@lem16684 (n = p) (m = (term4 m n)) h1). Qed.
Lemma lem230274 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : (term475 p m n) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term475 p m n => @lem230273 p m n h1) (fun h2 : term239 m n => @lem230272 p m n h1)). Qed.
Lemma lem230275 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : term239 m n.
Proof. exact (EQ_MP (@lem230274 p m n h1) (@lem230272 p m n h1)). Qed.
Lemma lem230276 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : term87 n p.
Proof. exact (@lem16597 (n = p) (m = (term4 m n)) h1). Qed.
Lemma lem230277 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : (term475 p m n) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term475 p m n => @lem230276 p m n h1) (fun h2 : term87 n p => @lem230272 p m n h1)). Qed.
Lemma lem230278 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : term87 n p.
Proof. exact (EQ_MP (@lem230277 p m n h1) (@lem230272 p m n h1)). Qed.
Lemma lem230279 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term87 n p) : term476 m n p.
Proof. exact (@lem16799 (m = (term4 m n)) (n = p) h1 h2). Qed.
Lemma lem230280 (p : nat) (m : nat) (n : nat) (h1 : term239 m n) (h2 : term475 p m n) : (term87 n p) = (term476 m n p).
Proof. exact (prop_ext (fun h3 : term87 n p => @lem230279 m n p h1 h3) (fun h3 : term476 m n p => @lem230278 p m n h2)). Qed.
Lemma lem230281 (p : nat) (m : nat) (n : nat) (h1 : term239 m n) (h2 : term475 p m n) : term476 m n p.
Proof. exact (EQ_MP (@lem230280 p m n h1 h2) (@lem230278 p m n h2)). Qed.
Lemma lem230282 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : (term239 m n) = (term476 m n p).
Proof. exact (prop_ext (fun h2 : term239 m n => @lem230281 p m n h2 h1) (fun h2 : term476 m n p => @lem230275 p m n h1)). Qed.
Lemma lem230283 (p : nat) (m : nat) (n : nat) (h1 : term475 p m n) : term476 m n p.
Proof. exact (EQ_MP (@lem230282 p m n h1) (@lem230275 p m n h1)). Qed.
Lemma lem230284 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term476 m n p.
Proof. exact (h1). Qed.
Lemma lem230285 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term87 n p.
Proof. exact (@lem16684 (m = (term4 m n)) (n = p) h1). Qed.
Lemma lem230286 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : (term476 m n p) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term476 m n p => @lem230285 m n p h1) (fun h2 : term87 n p => @lem230284 m n p h1)). Qed.
Lemma lem230287 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term87 n p.
Proof. exact (EQ_MP (@lem230286 m n p h1) (@lem230284 m n p h1)). Qed.
Lemma lem230288 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term239 m n.
Proof. exact (@lem16597 (m = (term4 m n)) (n = p) h1). Qed.
Lemma lem230289 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : (term476 m n p) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term476 m n p => @lem230288 m n p h1) (fun h2 : term239 m n => @lem230284 m n p h1)). Qed.
Lemma lem230290 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term239 m n.
Proof. exact (EQ_MP (@lem230289 m n p h1) (@lem230284 m n p h1)). Qed.
Lemma lem230291 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term87 n p) : term475 p m n.
Proof. exact (@lem16799 (n = p) (m = (term4 m n)) h2 h1). Qed.
Lemma lem230292 (m : nat) (n : nat) (p : nat) (h1 : term87 n p) (h2 : term476 m n p) : (term239 m n) = (term475 p m n).
Proof. exact (prop_ext (fun h3 : term239 m n => @lem230291 m n p h3 h1) (fun h3 : term475 p m n => @lem230290 m n p h2)). Qed.
Lemma lem230293 (m : nat) (n : nat) (p : nat) (h1 : term87 n p) (h2 : term476 m n p) : term475 p m n.
Proof. exact (EQ_MP (@lem230292 m n p h1 h2) (@lem230290 m n p h2)). Qed.
Lemma lem230294 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : (term87 n p) = (term475 p m n).
Proof. exact (prop_ext (fun h2 : term87 n p => @lem230293 m n p h2 h1) (fun h2 : term475 p m n => @lem230287 m n p h1)). Qed.
Lemma lem230295 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term475 p m n.
Proof. exact (EQ_MP (@lem230294 m n p h1) (@lem230287 m n p h1)). Qed.
Lemma lem230296 (p : nat) (m : nat) (n : nat) : term477 p m n.
Proof. exact (fun h0 : term476 m n p => @lem230295 m n p h0). Qed.
Lemma lem230297 (m : nat) (n : nat) (p : nat) : term478 m n p.
Proof. exact (fun h0 : term475 p m n => @lem230283 p m n h0). Qed.
Lemma lem230298 (p : nat) (m : nat) (n : nat) : term479 p m n.
Proof. exact (conj (@lem230297 m n p) (@lem230296 p m n)). Qed.
Lemma lem230299 (m : nat) (n : nat) (p : nat) : (term479 p m n) = ((term475 p m n) = (term476 m n p)).
Proof. exact (@lem32 (term475 p m n) (term476 m n p)). Qed.
Lemma lem230300 (m : nat) (n : nat) (p : nat) : (term475 p m n) = (term476 m n p).
Proof. exact (EQ_MP (@lem230299 m n p) (@lem230298 p m n)). Qed.
Lemma lem230301 (m : nat) (n : nat) (p : nat) (h1 : (term475 p m n) = (term476 m n p)) : (term474 p m n) = (term480 m n p).
Proof. exact (@lem16917 (term474 p m n) (term480 m n p) h1). Qed.
Lemma lem230302 (m : nat) (n : nat) (p : nat) : ((term475 p m n) = (term476 m n p)) = ((term474 p m n) = (term480 m n p)).
Proof. exact (prop_ext (fun h1 : (term475 p m n) = (term476 m n p) => @lem230301 m n p h1) (fun h1 : (term474 p m n) = (term480 m n p) => @lem230300 m n p)). Qed.
Lemma lem230303 (m : nat) (n : nat) (p : nat) : (term474 p m n) = (term480 m n p).
Proof. exact (EQ_MP (@lem230302 m n p) (@lem230300 m n p)). Qed.
Lemma lem230307 {_13060 : Type'} (__x : _13060) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem230309 {_13062 : Type'} (__x : _13062) (h1 : __x = __x) : __x = __x.
Proof. exact (h1). Qed.
Lemma lem230311 {_13062 : Type'} (__x : _13062) (__y : _13062) (h1 : __x = __y) : __x = __y.
Proof. exact (h1). Qed.
Lemma lem230312 {_13062 : Type'} : (@eq _13062) = (@eq _13062).
Proof. exact (eq_refl (@eq _13062)). Qed.
Lemma lem230313 {_13062 : Type'} (__x : _13062) (__y : _13062) (h1 : __x = __y) : (@eq _13062 __x) = (@eq _13062 __y).
Proof. exact (MK_COMB (@lem230312 _13062) (@lem230311 _13062 __x __y h1)). Qed.
Lemma lem230314 {_13062 : Type'} (__x : _13062) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem230315 {_13062 : Type'} (__x : _13062) (__y : _13062) (h1 : __x = __y) : (__x = __x) = (__y = __x).
Proof. exact (MK_COMB (@lem230313 _13062 __x __y h1) (@lem230314 _13062 __x)). Qed.
Lemma lem230316 {_13062 : Type'} (__x : _13062) (__y : _13062) (h1 : __x = __x) (h2 : __x = __y) : __y = __x.
Proof. exact (EQ_MP (@lem230315 _13062 __x __y h2) (@lem230309 _13062 __x h1)). Qed.
Lemma lem230317 {_13062 : Type'} (__x : _13062) (__y : _13062) (h1 : __x = __y) : term307 _13062 __y __x.
Proof. exact (fun h0 : __x = __x => @lem230316 _13062 __x __y h0 h1). Qed.
Lemma lem230318 {_13062 : Type'} (__x : _13062) : term308 _13062 __x.
Proof. exact (@lem22518 (__x = __x)). Qed.
Lemma lem230319 {_13062 : Type'} (__x : _13062) : (term308 _13062 __x) = (term309 _13062 __x).
Proof. exact (eq_refl (term308 _13062 __x)). Qed.
Lemma lem230320 {_13062 : Type'} (__x : _13062) : term309 _13062 __x.
Proof. exact (EQ_MP (@lem230319 _13062 __x) (@lem230318 _13062 __x)). Qed.
Lemma lem230321 {_13062 : Type'} (__y : _13062) (__x : _13062) : term310 _13062 __y __x.
Proof. exact (@lem230320 _13062 __x (__y = __x)). Qed.
Lemma lem230322 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term310 _13062 __y __x) = ((term307 _13062 __y __x) = (term311 _13062 __y __x)).
Proof. exact (eq_refl (term310 _13062 __y __x)). Qed.
Lemma lem230325 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term307 _13062 __y __x) = (term311 _13062 __y __x).
Proof. exact (EQ_MP (@lem230322 _13062 __y __x) (@lem230321 _13062 __y __x)). Qed.
Lemma lem230326 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term307 _13062 __y __x) = (term311 _13062 __y __x).
Proof. exact (@lem230325 _13062 __y __x). Qed.
Lemma lem230327 {_13062 : Type'} (__x : _13062) (__y : _13062) (h1 : __x = __y) : term311 _13062 __y __x.
Proof. exact (EQ_MP (@lem230326 _13062 __y __x) (@lem230317 _13062 __x __y h1)). Qed.
Lemma lem230328 {_13062 : Type'} (__y : _13062) (__x : _13062) : term312 _13062 __y __x.
Proof. exact (fun h0 : __x = __y => @lem230327 _13062 __x __y h0). Qed.
Lemma lem230329 {_13062 : Type'} (__x : _13062) (__y : _13062) : term313 _13062 __x __y.
Proof. exact (@lem22518 (__x = __y)). Qed.
Lemma lem230330 {_13062 : Type'} (__x : _13062) (__y : _13062) : (term313 _13062 __x __y) = (term314 _13062 __x __y).
Proof. exact (eq_refl (term313 _13062 __x __y)). Qed.
Lemma lem230331 {_13062 : Type'} (__x : _13062) (__y : _13062) : term314 _13062 __x __y.
Proof. exact (EQ_MP (@lem230330 _13062 __x __y) (@lem230329 _13062 __x __y)). Qed.
Lemma lem230332 {_13062 : Type'} (__y : _13062) (__x : _13062) : term315 _13062 __y __x.
Proof. exact (@lem230331 _13062 __x __y (term311 _13062 __y __x)). Qed.
Lemma lem230333 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term315 _13062 __y __x) = ((term312 _13062 __y __x) = (term316 _13062 __y __x)).
Proof. exact (eq_refl (term315 _13062 __y __x)). Qed.
Lemma lem230336 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term312 _13062 __y __x) = (term316 _13062 __y __x).
Proof. exact (EQ_MP (@lem230333 _13062 __y __x) (@lem230332 _13062 __y __x)). Qed.
Lemma lem230337 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term312 _13062 __y __x) = (term316 _13062 __y __x).
Proof. exact (@lem230336 _13062 __y __x). Qed.
Lemma lem230338 {_13062 : Type'} (__y : _13062) (__x : _13062) : term316 _13062 __y __x.
Proof. exact (EQ_MP (@lem230337 _13062 __y __x) (@lem230328 _13062 __y __x)). Qed.
Lemma lem230339 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term317 _13062 __y __x.
Proof. exact (h1). Qed.
Lemma lem230340 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term318 _13062 __y __x.
Proof. exact (@lem16684 (term319 _13062 __x __y) (term311 _13062 __y __x) h1). Qed.
Lemma lem230341 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : (term317 _13062 __y __x) = (term318 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term317 _13062 __y __x => @lem230340 _13062 __y __x h1) (fun h2 : term318 _13062 __y __x => @lem230339 _13062 __y __x h1)). Qed.
Lemma lem230342 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term318 _13062 __y __x.
Proof. exact (EQ_MP (@lem230341 _13062 __y __x h1) (@lem230339 _13062 __y __x h1)). Qed.
Lemma lem230343 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term320 _13062 __x __y.
Proof. exact (@lem16597 (term319 _13062 __x __y) (term311 _13062 __y __x) h1). Qed.
Lemma lem230344 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : (term317 _13062 __y __x) = (term320 _13062 __x __y).
Proof. exact (prop_ext (fun h2 : term317 _13062 __y __x => @lem230343 _13062 __y __x h1) (fun h2 : term320 _13062 __x __y => @lem230339 _13062 __y __x h1)). Qed.
Lemma lem230345 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term320 _13062 __x __y.
Proof. exact (EQ_MP (@lem230344 _13062 __y __x h1) (@lem230339 _13062 __y __x h1)). Qed.
Lemma lem230346 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term318 _13062 __y __x) : term319 _13062 __y __x.
Proof. exact (@lem16684 (term321 _13062 __x) (__y = __x) h1). Qed.
Lemma lem230347 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : (term318 _13062 __y __x) = (term319 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term318 _13062 __y __x => @lem230346 _13062 __y __x h2) (fun h2 : term319 _13062 __y __x => @lem230342 _13062 __y __x h1)). Qed.
Lemma lem230348 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term319 _13062 __y __x.
Proof. exact (EQ_MP (@lem230347 _13062 __y __x h1) (@lem230342 _13062 __y __x h1)). Qed.
Lemma lem230349 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term318 _13062 __y __x) : term322 _13062 __x.
Proof. exact (@lem16597 (term321 _13062 __x) (__y = __x) h1). Qed.
Lemma lem230350 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : (term318 _13062 __y __x) = (term322 _13062 __x).
Proof. exact (prop_ext (fun h2 : term318 _13062 __y __x => @lem230349 _13062 __y __x h2) (fun h2 : term322 _13062 __x => @lem230342 _13062 __y __x h1)). Qed.
Lemma lem230351 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term322 _13062 __x.
Proof. exact (EQ_MP (@lem230350 _13062 __y __x h1) (@lem230342 _13062 __y __x h1)). Qed.
Lemma lem230352 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term320 _13062 __x __y) (h2 : term319 _13062 __y __x) : term323 _13062 __y __x.
Proof. exact (@lem16799 (term319 _13062 __x __y) (__y = __x) h1 h2). Qed.
Lemma lem230353 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term320 _13062 __x __y) (h2 : term317 _13062 __y __x) : (term319 _13062 __y __x) = (term323 _13062 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _13062 __y __x => @lem230352 _13062 __y __x h1 h3) (fun h3 : term323 _13062 __y __x => @lem230348 _13062 __y __x h2)). Qed.
Lemma lem230354 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term320 _13062 __x __y) (h2 : term317 _13062 __y __x) : term323 _13062 __y __x.
Proof. exact (EQ_MP (@lem230353 _13062 __y __x h1 h2) (@lem230348 _13062 __y __x h2)). Qed.
Lemma lem230355 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : (term320 _13062 __x __y) = (term323 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _13062 __x __y => @lem230354 _13062 __y __x h2 h1) (fun h2 : term323 _13062 __y __x => @lem230345 _13062 __y __x h1)). Qed.
Lemma lem230356 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term323 _13062 __y __x.
Proof. exact (EQ_MP (@lem230355 _13062 __y __x h1) (@lem230345 _13062 __y __x h1)). Qed.
Lemma lem230357 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term322 _13062 __x) (h2 : term323 _13062 __y __x) : term324 _13062 __y __x.
Proof. exact (@lem16799 (term321 _13062 __x) (term325 _13062 __y __x) h1 h2). Qed.
Lemma lem230358 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term322 _13062 __x) (h2 : term317 _13062 __y __x) : (term323 _13062 __y __x) = (term324 _13062 __y __x).
Proof. exact (prop_ext (fun h3 : term323 _13062 __y __x => @lem230357 _13062 __y __x h1 h3) (fun h3 : term324 _13062 __y __x => @lem230356 _13062 __y __x h2)). Qed.
Lemma lem230359 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term322 _13062 __x) (h2 : term317 _13062 __y __x) : term324 _13062 __y __x.
Proof. exact (EQ_MP (@lem230358 _13062 __y __x h1 h2) (@lem230356 _13062 __y __x h2)). Qed.
Lemma lem230360 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : (term322 _13062 __x) = (term324 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _13062 __x => @lem230359 _13062 __y __x h2 h1) (fun h2 : term324 _13062 __y __x => @lem230351 _13062 __y __x h1)). Qed.
Lemma lem230361 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term317 _13062 __y __x) : term324 _13062 __y __x.
Proof. exact (EQ_MP (@lem230360 _13062 __y __x h1) (@lem230351 _13062 __y __x h1)). Qed.
Lemma lem230362 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term324 _13062 __y __x.
Proof. exact (h1). Qed.
Lemma lem230363 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term323 _13062 __y __x.
Proof. exact (@lem16684 (term321 _13062 __x) (term325 _13062 __y __x) h1). Qed.
Lemma lem230364 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : (term324 _13062 __y __x) = (term323 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term324 _13062 __y __x => @lem230363 _13062 __y __x h1) (fun h2 : term323 _13062 __y __x => @lem230362 _13062 __y __x h1)). Qed.
Lemma lem230365 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term323 _13062 __y __x.
Proof. exact (EQ_MP (@lem230364 _13062 __y __x h1) (@lem230362 _13062 __y __x h1)). Qed.
Lemma lem230366 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term322 _13062 __x.
Proof. exact (@lem16597 (term321 _13062 __x) (term325 _13062 __y __x) h1). Qed.
Lemma lem230367 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : (term324 _13062 __y __x) = (term322 _13062 __x).
Proof. exact (prop_ext (fun h2 : term324 _13062 __y __x => @lem230366 _13062 __y __x h1) (fun h2 : term322 _13062 __x => @lem230362 _13062 __y __x h1)). Qed.
Lemma lem230368 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term322 _13062 __x.
Proof. exact (EQ_MP (@lem230367 _13062 __y __x h1) (@lem230362 _13062 __y __x h1)). Qed.
Lemma lem230369 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term323 _13062 __y __x) : term319 _13062 __y __x.
Proof. exact (@lem16684 (term319 _13062 __x __y) (__y = __x) h1). Qed.
Lemma lem230370 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : (term323 _13062 __y __x) = (term319 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term323 _13062 __y __x => @lem230369 _13062 __y __x h2) (fun h2 : term319 _13062 __y __x => @lem230365 _13062 __y __x h1)). Qed.
Lemma lem230371 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term319 _13062 __y __x.
Proof. exact (EQ_MP (@lem230370 _13062 __y __x h1) (@lem230365 _13062 __y __x h1)). Qed.
Lemma lem230372 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term323 _13062 __y __x) : term320 _13062 __x __y.
Proof. exact (@lem16597 (term319 _13062 __x __y) (__y = __x) h1). Qed.
Lemma lem230373 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : (term323 _13062 __y __x) = (term320 _13062 __x __y).
Proof. exact (prop_ext (fun h2 : term323 _13062 __y __x => @lem230372 _13062 __y __x h2) (fun h2 : term320 _13062 __x __y => @lem230365 _13062 __y __x h1)). Qed.
Lemma lem230374 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term320 _13062 __x __y.
Proof. exact (EQ_MP (@lem230373 _13062 __y __x h1) (@lem230365 _13062 __y __x h1)). Qed.
Lemma lem230375 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term322 _13062 __x) (h2 : term319 _13062 __y __x) : term318 _13062 __y __x.
Proof. exact (@lem16799 (term321 _13062 __x) (__y = __x) h1 h2). Qed.
Lemma lem230376 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term322 _13062 __x) (h2 : term324 _13062 __y __x) : (term319 _13062 __y __x) = (term318 _13062 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _13062 __y __x => @lem230375 _13062 __y __x h1 h3) (fun h3 : term318 _13062 __y __x => @lem230371 _13062 __y __x h2)). Qed.
Lemma lem230377 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term322 _13062 __x) (h2 : term324 _13062 __y __x) : term318 _13062 __y __x.
Proof. exact (EQ_MP (@lem230376 _13062 __y __x h1 h2) (@lem230371 _13062 __y __x h2)). Qed.
Lemma lem230378 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : (term322 _13062 __x) = (term318 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _13062 __x => @lem230377 _13062 __y __x h2 h1) (fun h2 : term318 _13062 __y __x => @lem230368 _13062 __y __x h1)). Qed.
Lemma lem230379 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term318 _13062 __y __x.
Proof. exact (EQ_MP (@lem230378 _13062 __y __x h1) (@lem230368 _13062 __y __x h1)). Qed.
Lemma lem230380 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term320 _13062 __x __y) (h2 : term318 _13062 __y __x) : term317 _13062 __y __x.
Proof. exact (@lem16799 (term319 _13062 __x __y) (term311 _13062 __y __x) h1 h2). Qed.
Lemma lem230381 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term320 _13062 __x __y) (h2 : term324 _13062 __y __x) : (term318 _13062 __y __x) = (term317 _13062 __y __x).
Proof. exact (prop_ext (fun h3 : term318 _13062 __y __x => @lem230380 _13062 __y __x h1 h3) (fun h3 : term317 _13062 __y __x => @lem230379 _13062 __y __x h2)). Qed.
Lemma lem230382 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term320 _13062 __x __y) (h2 : term324 _13062 __y __x) : term317 _13062 __y __x.
Proof. exact (EQ_MP (@lem230381 _13062 __y __x h1 h2) (@lem230379 _13062 __y __x h2)). Qed.
Lemma lem230383 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : (term320 _13062 __x __y) = (term317 _13062 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _13062 __x __y => @lem230382 _13062 __y __x h2 h1) (fun h2 : term317 _13062 __y __x => @lem230374 _13062 __y __x h1)). Qed.
Lemma lem230384 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : term324 _13062 __y __x) : term317 _13062 __y __x.
Proof. exact (EQ_MP (@lem230383 _13062 __y __x h1) (@lem230374 _13062 __y __x h1)). Qed.
Lemma lem230385 {_13062 : Type'} (__y : _13062) (__x : _13062) : term326 _13062 __y __x.
Proof. exact (fun h0 : term324 _13062 __y __x => @lem230384 _13062 __y __x h0). Qed.
Lemma lem230386 {_13062 : Type'} (__y : _13062) (__x : _13062) : term327 _13062 __y __x.
Proof. exact (fun h0 : term317 _13062 __y __x => @lem230361 _13062 __y __x h0). Qed.
Lemma lem230387 {_13062 : Type'} (__y : _13062) (__x : _13062) : term328 _13062 __y __x.
Proof. exact (conj (@lem230386 _13062 __y __x) (@lem230385 _13062 __y __x)). Qed.
Lemma lem230388 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term328 _13062 __y __x) = ((term317 _13062 __y __x) = (term324 _13062 __y __x)).
Proof. exact (@lem32 (term317 _13062 __y __x) (term324 _13062 __y __x)). Qed.
Lemma lem230389 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term317 _13062 __y __x) = (term324 _13062 __y __x).
Proof. exact (EQ_MP (@lem230388 _13062 __y __x) (@lem230387 _13062 __y __x)). Qed.
Lemma lem230390 {_13062 : Type'} (__y : _13062) (__x : _13062) (h1 : (term317 _13062 __y __x) = (term324 _13062 __y __x)) : (term316 _13062 __y __x) = (term329 _13062 __y __x).
Proof. exact (@lem16917 (term316 _13062 __y __x) (term329 _13062 __y __x) h1). Qed.
Lemma lem230391 {_13062 : Type'} (__y : _13062) (__x : _13062) : ((term317 _13062 __y __x) = (term324 _13062 __y __x)) = ((term316 _13062 __y __x) = (term329 _13062 __y __x)).
Proof. exact (prop_ext (fun h1 : (term317 _13062 __y __x) = (term324 _13062 __y __x) => @lem230390 _13062 __y __x h1) (fun h1 : (term316 _13062 __y __x) = (term329 _13062 __y __x) => @lem230389 _13062 __y __x)). Qed.
Lemma lem230392 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term316 _13062 __y __x) = (term329 _13062 __y __x).
Proof. exact (EQ_MP (@lem230391 _13062 __y __x) (@lem230389 _13062 __y __x)). Qed.
Lemma lem230393 {_13062 : Type'} (__y : _13062) (__x : _13062) : term329 _13062 __y __x.
Proof. exact (EQ_MP (@lem230392 _13062 __y __x) (@lem230338 _13062 __y __x)). Qed.
Lemma lem230394 {_13062 : Type'} (__y : _13062) (__x : _13062) : term329 _13062 __y __x.
Proof. exact (@lem230393 _13062 __y __x). Qed.
Lemma lem230395 {_13062 : Type'} (__x : _13062) : __x = __x.
Proof. exact (@lem230307 _13062 __x). Qed.
Lemma lem230398 {_13062 : Type'} (__x : _13062) : (__x = __x) = (__x = __x).
Proof. exact (eq_refl (__x = __x)). Qed.
Lemma lem230399 {_13062 : Type'} (__x : _13062) : (__x = __x) = (__x = __x).
Proof. exact (@lem230398 _13062 __x). Qed.
Lemma lem230400 {_13062 : Type'} (__x : _13062) : __x = __x.
Proof. exact (EQ_MP (@lem230399 _13062 __x) (@lem230395 _13062 __x)). Qed.
Lemma lem230403 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term329 _13062 __y __x) = (term329 _13062 __y __x).
Proof. exact (eq_refl (term329 _13062 __y __x)). Qed.
Lemma lem230404 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term329 _13062 __y __x) = (term329 _13062 __y __x).
Proof. exact (@lem230403 _13062 __y __x). Qed.
Lemma lem230405 {_13062 : Type'} (__y : _13062) (__x : _13062) : term329 _13062 __y __x.
Proof. exact (EQ_MP (@lem230404 _13062 __y __x) (@lem230394 _13062 __y __x)). Qed.
Lemma lem230406 {_13062 : Type'} (__x : _13062) : term330 _13062 __x.
Proof. exact (@lem22025 (__x = __x)). Qed.
Lemma lem230407 {_13062 : Type'} (__x : _13062) : (term330 _13062 __x) = (term331 _13062 __x).
Proof. exact (eq_refl (term330 _13062 __x)). Qed.
Lemma lem230408 {_13062 : Type'} (__x : _13062) : term331 _13062 __x.
Proof. exact (EQ_MP (@lem230407 _13062 __x) (@lem230406 _13062 __x)). Qed.
Lemma lem230409 {_13062 : Type'} (__y : _13062) (__x : _13062) : term332 _13062 __y __x.
Proof. exact (@lem230408 _13062 __x (term325 _13062 __y __x)). Qed.
Lemma lem230410 {_13062 : Type'} (__y : _13062) (__x : _13062) : (term332 _13062 __y __x) = (term333 _13062 __y __x).
Proof. exact (eq_refl (term332 _13062 __y __x)). Qed.
Lemma lem230411 {_13062 : Type'} (__y : _13062) (__x : _13062) : term333 _13062 __y __x.
Proof. exact (EQ_MP (@lem230410 _13062 __y __x) (@lem230409 _13062 __y __x)). Qed.
Lemma lem230412 {_13062 : Type'} (__y : _13062) (__x : _13062) : term334 _13062 __y __x.
Proof. exact (@lem230411 _13062 __y __x (@lem230400 _13062 __x)). Qed.
Lemma lem230415 {_13062 : Type'} (__y : _13062) (__x : _13062) : term325 _13062 __y __x.
Proof. exact (@lem230412 _13062 __y __x (@lem230405 _13062 __y __x)). Qed.
Lemma lem230416 (__y : nat) (__x : nat) : term335 __y __x.
Proof. exact (@lem230415 nat __y __x). Qed.
Lemma lem230423 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term480 m n p.
Proof. exact (EQ_MP (@lem230303 m n p) (@lem230271 m n p h1 h2 h3)). Qed.
Lemma lem230427 (n : nat) (m : nat) : term481 n m.
Proof. exact (@lem230416 (term4 m n) m). Qed.
Lemma lem230428 (m : nat) (n : nat) : term482 m n.
Proof. exact (@lem22288 (m = (term4 m n))). Qed.
Lemma lem230429 (m : nat) (n : nat) : (term482 m n) = (term483 m n).
Proof. exact (eq_refl (term482 m n)). Qed.
Lemma lem230430 (m : nat) (n : nat) : term483 m n.
Proof. exact (EQ_MP (@lem230429 m n) (@lem230428 m n)). Qed.
Lemma lem230431 (m : nat) (n : nat) (p : nat) : term484 m n p.
Proof. exact (@lem230430 m n (n = p)). Qed.
Lemma lem230432 (m : nat) (n : nat) (p : nat) : (term484 m n p) = (term485 m n p).
Proof. exact (eq_refl (term484 m n p)). Qed.
Lemma lem230433 (m : nat) (n : nat) (p : nat) : term485 m n p.
Proof. exact (EQ_MP (@lem230432 m n p) (@lem230431 m n p)). Qed.
Lemma lem230434 (p : nat) (n : nat) (m : nat) : term486 p n m.
Proof. exact (@lem230433 m n p ((term4 m n) = m)). Qed.
Lemma lem230435 (p : nat) (n : nat) (m : nat) : (term486 p n m) = (term487 p n m).
Proof. exact (eq_refl (term486 p n m)). Qed.
Lemma lem230436 (p : nat) (n : nat) (m : nat) : term487 p n m.
Proof. exact (EQ_MP (@lem230435 p n m) (@lem230434 p n m)). Qed.
Lemma lem230437 (n : nat) (m : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term488 p n m.
Proof. exact (@lem230436 p n m (@lem230423 m n p h1 h2 h3)). Qed.
Lemma lem230440 (n : nat) (m : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term489 p n m.
Proof. exact (@lem230437 n m p h1 h2 h3 (@lem230427 n m)). Qed.
Lemma lem230442 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem230444 (n : nat) (m : nat) (h1 : (term4 m n) = m) : (term4 m n) = m.
Proof. exact (h1). Qed.
Lemma lem230445 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem230446 (n : nat) (m : nat) (h1 : (term4 m n) = m) : (m = (term4 m n)) = (m = m).
Proof. exact (MK_COMB (@lem230445 m) (@lem230444 n m h1)). Qed.
Lemma lem230447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem230448 (n : nat) (m : nat) (h1 : (term4 m n) = m) : (term239 m n) = (term490 m).
Proof. exact (MK_COMB (@lem230447) (@lem230446 n m h1)). Qed.
Lemma lem230449 (n : nat) (m : nat) (h1 : term239 m n) (h2 : (term4 m n) = m) : term490 m.
Proof. exact (EQ_MP (@lem230448 n m h2) (@lem230442 m n h1)). Qed.
Lemma lem230450 (n : nat) (m : nat) (h1 : (term4 m n) = m) : term491 n m.
Proof. exact (fun h0 : term239 m n => @lem230449 n m h0 h1). Qed.
Lemma lem230451 (m : nat) (n : nat) : term434 m n.
Proof. exact (@lem22403 (m = (term4 m n))). Qed.
Lemma lem230452 (m : nat) (n : nat) : (term434 m n) = (term435 m n).
Proof. exact (eq_refl (term434 m n)). Qed.
Lemma lem230453 (m : nat) (n : nat) : term435 m n.
Proof. exact (EQ_MP (@lem230452 m n) (@lem230451 m n)). Qed.
Lemma lem230454 (n : nat) (m : nat) : term492 n m.
Proof. exact (@lem230453 m n (term490 m)). Qed.
Lemma lem230455 (n : nat) (m : nat) : (term492 n m) = ((term491 n m) = (term493 n m)).
Proof. exact (eq_refl (term492 n m)). Qed.
Lemma lem230458 (n : nat) (m : nat) : (term491 n m) = (term493 n m).
Proof. exact (EQ_MP (@lem230455 n m) (@lem230454 n m)). Qed.
Lemma lem230459 (n : nat) (m : nat) (h1 : (term4 m n) = m) : term493 n m.
Proof. exact (EQ_MP (@lem230458 n m) (@lem230450 n m h1)). Qed.
Lemma lem230460 (n : nat) (m : nat) : term494 n m.
Proof. exact (fun h0 : (term4 m n) = m => @lem230459 n m h0). Qed.
Lemma lem230461 (n : nat) (m : nat) : term495 n m.
Proof. exact (@lem22518 ((term4 m n) = m)). Qed.
Lemma lem230462 (n : nat) (m : nat) : (term495 n m) = (term496 n m).
Proof. exact (eq_refl (term495 n m)). Qed.
Lemma lem230463 (n : nat) (m : nat) : term496 n m.
Proof. exact (EQ_MP (@lem230462 n m) (@lem230461 n m)). Qed.
Lemma lem230464 (n : nat) (m : nat) : term497 n m.
Proof. exact (@lem230463 n m (term493 n m)). Qed.
Lemma lem230465 (n : nat) (m : nat) : (term497 n m) = ((term494 n m) = (term498 n m)).
Proof. exact (eq_refl (term497 n m)). Qed.
Lemma lem230468 (n : nat) (m : nat) : (term494 n m) = (term498 n m).
Proof. exact (EQ_MP (@lem230465 n m) (@lem230464 n m)). Qed.
Lemma lem230469 (n : nat) (m : nat) : term498 n m.
Proof. exact (EQ_MP (@lem230468 n m) (@lem230460 n m)). Qed.
Lemma lem230470 (n : nat) (m : nat) (h1 : term499 n m) : term499 n m.
Proof. exact (h1). Qed.
Lemma lem230471 (n : nat) (m : nat) (h1 : term499 n m) : term500 n m.
Proof. exact (@lem16684 (term501 n m) (term493 n m) h1). Qed.
Lemma lem230472 (n : nat) (m : nat) (h1 : term499 n m) : (term499 n m) = (term500 n m).
Proof. exact (prop_ext (fun h2 : term499 n m => @lem230471 n m h1) (fun h2 : term500 n m => @lem230470 n m h1)). Qed.
Lemma lem230473 (n : nat) (m : nat) (h1 : term499 n m) : term500 n m.
Proof. exact (EQ_MP (@lem230472 n m h1) (@lem230470 n m h1)). Qed.
Lemma lem230474 (n : nat) (m : nat) (h1 : term499 n m) : term502 n m.
Proof. exact (@lem16597 (term501 n m) (term493 n m) h1). Qed.
Lemma lem230475 (n : nat) (m : nat) (h1 : term499 n m) : (term499 n m) = (term502 n m).
Proof. exact (prop_ext (fun h2 : term499 n m => @lem230474 n m h1) (fun h2 : term502 n m => @lem230470 n m h1)). Qed.
Lemma lem230476 (n : nat) (m : nat) (h1 : term499 n m) : term502 n m.
Proof. exact (EQ_MP (@lem230475 n m h1) (@lem230470 n m h1)). Qed.
Lemma lem230477 (n : nat) (m : nat) (h1 : term500 n m) : term503 m.
Proof. exact (@lem16684 (m = (term4 m n)) (term490 m) h1). Qed.
Lemma lem230478 (n : nat) (m : nat) (h1 : term499 n m) : (term500 n m) = (term503 m).
Proof. exact (prop_ext (fun h2 : term500 n m => @lem230477 n m h2) (fun h2 : term503 m => @lem230473 n m h1)). Qed.
Lemma lem230479 (n : nat) (m : nat) (h1 : term499 n m) : term503 m.
Proof. exact (EQ_MP (@lem230478 n m h1) (@lem230473 n m h1)). Qed.
Lemma lem230480 (n : nat) (m : nat) (h1 : term500 n m) : term239 m n.
Proof. exact (@lem16597 (m = (term4 m n)) (term490 m) h1). Qed.
Lemma lem230481 (n : nat) (m : nat) (h1 : term499 n m) : (term500 n m) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term500 n m => @lem230480 n m h2) (fun h2 : term239 m n => @lem230473 n m h1)). Qed.
Lemma lem230482 (n : nat) (m : nat) (h1 : term499 n m) : term239 m n.
Proof. exact (EQ_MP (@lem230481 n m h1) (@lem230473 n m h1)). Qed.
Lemma lem230483 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term239 m n) : term504 m n.
Proof. exact (@lem16799 (term501 n m) (m = (term4 m n)) h1 h2). Qed.
Lemma lem230484 (n : nat) (m : nat) (h1 : term502 n m) (h2 : term499 n m) : (term239 m n) = (term504 m n).
Proof. exact (prop_ext (fun h3 : term239 m n => @lem230483 m n h1 h3) (fun h3 : term504 m n => @lem230482 n m h2)). Qed.
Lemma lem230485 (n : nat) (m : nat) (h1 : term502 n m) (h2 : term499 n m) : term504 m n.
Proof. exact (EQ_MP (@lem230484 n m h1 h2) (@lem230482 n m h2)). Qed.
Lemma lem230486 (n : nat) (m : nat) (h1 : term499 n m) : (term502 n m) = (term504 m n).
Proof. exact (prop_ext (fun h2 : term502 n m => @lem230485 n m h2 h1) (fun h2 : term504 m n => @lem230476 n m h1)). Qed.
Lemma lem230487 (n : nat) (m : nat) (h1 : term499 n m) : term504 m n.
Proof. exact (EQ_MP (@lem230486 n m h1) (@lem230476 n m h1)). Qed.
Lemma lem230488 (m : nat) (n : nat) (h1 : term503 m) (h2 : term504 m n) : term505 m n.
Proof. exact (@lem16799 (term490 m) (term506 m n) h1 h2). Qed.
Lemma lem230489 (n : nat) (m : nat) (h1 : term503 m) (h2 : term499 n m) : (term504 m n) = (term505 m n).
Proof. exact (prop_ext (fun h3 : term504 m n => @lem230488 m n h1 h3) (fun h3 : term505 m n => @lem230487 n m h2)). Qed.
Lemma lem230490 (n : nat) (m : nat) (h1 : term503 m) (h2 : term499 n m) : term505 m n.
Proof. exact (EQ_MP (@lem230489 n m h1 h2) (@lem230487 n m h2)). Qed.
Lemma lem230491 (n : nat) (m : nat) (h1 : term499 n m) : (term503 m) = (term505 m n).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230490 n m h2 h1) (fun h2 : term505 m n => @lem230479 n m h1)). Qed.
Lemma lem230492 (n : nat) (m : nat) (h1 : term499 n m) : term505 m n.
Proof. exact (EQ_MP (@lem230491 n m h1) (@lem230479 n m h1)). Qed.
Lemma lem230493 (m : nat) (n : nat) (h1 : term505 m n) : term505 m n.
Proof. exact (h1). Qed.
Lemma lem230494 (m : nat) (n : nat) (h1 : term505 m n) : term504 m n.
Proof. exact (@lem16684 (term490 m) (term506 m n) h1). Qed.
Lemma lem230495 (m : nat) (n : nat) (h1 : term505 m n) : (term505 m n) = (term504 m n).
Proof. exact (prop_ext (fun h2 : term505 m n => @lem230494 m n h1) (fun h2 : term504 m n => @lem230493 m n h1)). Qed.
Lemma lem230496 (m : nat) (n : nat) (h1 : term505 m n) : term504 m n.
Proof. exact (EQ_MP (@lem230495 m n h1) (@lem230493 m n h1)). Qed.
Lemma lem230497 (m : nat) (n : nat) (h1 : term505 m n) : term503 m.
Proof. exact (@lem16597 (term490 m) (term506 m n) h1). Qed.
Lemma lem230498 (m : nat) (n : nat) (h1 : term505 m n) : (term505 m n) = (term503 m).
Proof. exact (prop_ext (fun h2 : term505 m n => @lem230497 m n h1) (fun h2 : term503 m => @lem230493 m n h1)). Qed.
Lemma lem230499 (m : nat) (n : nat) (h1 : term505 m n) : term503 m.
Proof. exact (EQ_MP (@lem230498 m n h1) (@lem230493 m n h1)). Qed.
Lemma lem230500 (m : nat) (n : nat) (h1 : term504 m n) : term239 m n.
Proof. exact (@lem16684 (term501 n m) (m = (term4 m n)) h1). Qed.
Lemma lem230501 (m : nat) (n : nat) (h1 : term505 m n) : (term504 m n) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term504 m n => @lem230500 m n h2) (fun h2 : term239 m n => @lem230496 m n h1)). Qed.
Lemma lem230502 (m : nat) (n : nat) (h1 : term505 m n) : term239 m n.
Proof. exact (EQ_MP (@lem230501 m n h1) (@lem230496 m n h1)). Qed.
Lemma lem230503 (m : nat) (n : nat) (h1 : term504 m n) : term502 n m.
Proof. exact (@lem16597 (term501 n m) (m = (term4 m n)) h1). Qed.
Lemma lem230504 (m : nat) (n : nat) (h1 : term505 m n) : (term504 m n) = (term502 n m).
Proof. exact (prop_ext (fun h2 : term504 m n => @lem230503 m n h2) (fun h2 : term502 n m => @lem230496 m n h1)). Qed.
Lemma lem230505 (m : nat) (n : nat) (h1 : term505 m n) : term502 n m.
Proof. exact (EQ_MP (@lem230504 m n h1) (@lem230496 m n h1)). Qed.
Lemma lem230506 (m : nat) (n : nat) (h1 : term503 m) (h2 : term239 m n) : term500 n m.
Proof. exact (@lem16799 (m = (term4 m n)) (term490 m) h2 h1). Qed.
Lemma lem230507 (m : nat) (n : nat) (h1 : term239 m n) (h2 : term505 m n) : (term503 m) = (term500 n m).
Proof. exact (prop_ext (fun h3 : term503 m => @lem230506 m n h3 h1) (fun h3 : term500 n m => @lem230499 m n h2)). Qed.
Lemma lem230508 (m : nat) (n : nat) (h1 : term239 m n) (h2 : term505 m n) : term500 n m.
Proof. exact (EQ_MP (@lem230507 m n h1 h2) (@lem230499 m n h2)). Qed.
Lemma lem230509 (m : nat) (n : nat) (h1 : term505 m n) : (term239 m n) = (term500 n m).
Proof. exact (prop_ext (fun h2 : term239 m n => @lem230508 m n h2 h1) (fun h2 : term500 n m => @lem230502 m n h1)). Qed.
Lemma lem230510 (m : nat) (n : nat) (h1 : term505 m n) : term500 n m.
Proof. exact (EQ_MP (@lem230509 m n h1) (@lem230502 m n h1)). Qed.
Lemma lem230511 (n : nat) (m : nat) (h1 : term502 n m) (h2 : term500 n m) : term499 n m.
Proof. exact (@lem16799 (term501 n m) (term493 n m) h1 h2). Qed.
Lemma lem230512 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term505 m n) : (term500 n m) = (term499 n m).
Proof. exact (prop_ext (fun h3 : term500 n m => @lem230511 n m h1 h3) (fun h3 : term499 n m => @lem230510 m n h2)). Qed.
Lemma lem230513 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term505 m n) : term499 n m.
Proof. exact (EQ_MP (@lem230512 m n h1 h2) (@lem230510 m n h2)). Qed.
Lemma lem230514 (m : nat) (n : nat) (h1 : term505 m n) : (term502 n m) = (term499 n m).
Proof. exact (prop_ext (fun h2 : term502 n m => @lem230513 m n h2 h1) (fun h2 : term499 n m => @lem230505 m n h1)). Qed.
Lemma lem230515 (m : nat) (n : nat) (h1 : term505 m n) : term499 n m.
Proof. exact (EQ_MP (@lem230514 m n h1) (@lem230505 m n h1)). Qed.
Lemma lem230516 (n : nat) (m : nat) : term507 n m.
Proof. exact (fun h0 : term505 m n => @lem230515 m n h0). Qed.
Lemma lem230517 (m : nat) (n : nat) : term508 m n.
Proof. exact (fun h0 : term499 n m => @lem230492 n m h0). Qed.
Lemma lem230518 (n : nat) (m : nat) : term509 n m.
Proof. exact (conj (@lem230517 m n) (@lem230516 n m)). Qed.
Lemma lem230519 (m : nat) (n : nat) : (term509 n m) = ((term499 n m) = (term505 m n)).
Proof. exact (@lem32 (term499 n m) (term505 m n)). Qed.
Lemma lem230520 (m : nat) (n : nat) : (term499 n m) = (term505 m n).
Proof. exact (EQ_MP (@lem230519 m n) (@lem230518 n m)). Qed.
Lemma lem230521 (m : nat) (n : nat) (h1 : (term499 n m) = (term505 m n)) : (term498 n m) = (term510 m n).
Proof. exact (@lem16917 (term498 n m) (term510 m n) h1). Qed.
Lemma lem230522 (m : nat) (n : nat) : ((term499 n m) = (term505 m n)) = ((term498 n m) = (term510 m n)).
Proof. exact (prop_ext (fun h1 : (term499 n m) = (term505 m n) => @lem230521 m n h1) (fun h1 : (term498 n m) = (term510 m n) => @lem230520 m n)). Qed.
Lemma lem230523 (m : nat) (n : nat) : (term498 n m) = (term510 m n).
Proof. exact (EQ_MP (@lem230522 m n) (@lem230520 m n)). Qed.
Lemma lem230524 (m : nat) (n : nat) : term510 m n.
Proof. exact (EQ_MP (@lem230523 m n) (@lem230469 n m)). Qed.
Lemma lem230525 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : term511 p n m.
Proof. exact (h1). Qed.
Lemma lem230526 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : term501 n m.
Proof. exact (@lem16684 (n = p) ((term4 m n) = m) h1). Qed.
Lemma lem230527 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : (term511 p n m) = (term501 n m).
Proof. exact (prop_ext (fun h2 : term511 p n m => @lem230526 p n m h1) (fun h2 : term501 n m => @lem230525 p n m h1)). Qed.
Lemma lem230528 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : term501 n m.
Proof. exact (EQ_MP (@lem230527 p n m h1) (@lem230525 p n m h1)). Qed.
Lemma lem230529 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : term87 n p.
Proof. exact (@lem16597 (n = p) ((term4 m n) = m) h1). Qed.
Lemma lem230530 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : (term511 p n m) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term511 p n m => @lem230529 p n m h1) (fun h2 : term87 n p => @lem230525 p n m h1)). Qed.
Lemma lem230531 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : term87 n p.
Proof. exact (EQ_MP (@lem230530 p n m h1) (@lem230525 p n m h1)). Qed.
Lemma lem230532 (p : nat) (n : nat) (m : nat) (h1 : term87 n p) (h2 : term501 n m) : term512 m n p.
Proof. exact (@lem16799 ((term4 m n) = m) (n = p) h2 h1). Qed.
Lemma lem230533 (p : nat) (n : nat) (m : nat) (h1 : term501 n m) (h2 : term511 p n m) : (term87 n p) = (term512 m n p).
Proof. exact (prop_ext (fun h3 : term87 n p => @lem230532 p n m h3 h1) (fun h3 : term512 m n p => @lem230531 p n m h2)). Qed.
Lemma lem230534 (p : nat) (n : nat) (m : nat) (h1 : term501 n m) (h2 : term511 p n m) : term512 m n p.
Proof. exact (EQ_MP (@lem230533 p n m h1 h2) (@lem230531 p n m h2)). Qed.
Lemma lem230535 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : (term501 n m) = (term512 m n p).
Proof. exact (prop_ext (fun h2 : term501 n m => @lem230534 p n m h2 h1) (fun h2 : term512 m n p => @lem230528 p n m h1)). Qed.
Lemma lem230536 (p : nat) (n : nat) (m : nat) (h1 : term511 p n m) : term512 m n p.
Proof. exact (EQ_MP (@lem230535 p n m h1) (@lem230528 p n m h1)). Qed.
Lemma lem230537 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : term512 m n p.
Proof. exact (h1). Qed.
Lemma lem230538 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : term87 n p.
Proof. exact (@lem16684 ((term4 m n) = m) (n = p) h1). Qed.
Lemma lem230539 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : (term512 m n p) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term512 m n p => @lem230538 m n p h1) (fun h2 : term87 n p => @lem230537 m n p h1)). Qed.
Lemma lem230540 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : term87 n p.
Proof. exact (EQ_MP (@lem230539 m n p h1) (@lem230537 m n p h1)). Qed.
Lemma lem230541 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : term501 n m.
Proof. exact (@lem16597 ((term4 m n) = m) (n = p) h1). Qed.
Lemma lem230542 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : (term512 m n p) = (term501 n m).
Proof. exact (prop_ext (fun h2 : term512 m n p => @lem230541 m n p h1) (fun h2 : term501 n m => @lem230537 m n p h1)). Qed.
Lemma lem230543 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : term501 n m.
Proof. exact (EQ_MP (@lem230542 m n p h1) (@lem230537 m n p h1)). Qed.
Lemma lem230544 (p : nat) (n : nat) (m : nat) (h1 : term87 n p) (h2 : term501 n m) : term511 p n m.
Proof. exact (@lem16799 (n = p) ((term4 m n) = m) h1 h2). Qed.
Lemma lem230545 (m : nat) (n : nat) (p : nat) (h1 : term87 n p) (h2 : term512 m n p) : (term501 n m) = (term511 p n m).
Proof. exact (prop_ext (fun h3 : term501 n m => @lem230544 p n m h1 h3) (fun h3 : term511 p n m => @lem230543 m n p h2)). Qed.
Lemma lem230546 (m : nat) (n : nat) (p : nat) (h1 : term87 n p) (h2 : term512 m n p) : term511 p n m.
Proof. exact (EQ_MP (@lem230545 m n p h1 h2) (@lem230543 m n p h2)). Qed.
Lemma lem230547 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : (term87 n p) = (term511 p n m).
Proof. exact (prop_ext (fun h2 : term87 n p => @lem230546 m n p h2 h1) (fun h2 : term511 p n m => @lem230540 m n p h1)). Qed.
Lemma lem230548 (m : nat) (n : nat) (p : nat) (h1 : term512 m n p) : term511 p n m.
Proof. exact (EQ_MP (@lem230547 m n p h1) (@lem230540 m n p h1)). Qed.
Lemma lem230549 (p : nat) (n : nat) (m : nat) : term513 p n m.
Proof. exact (fun h0 : term512 m n p => @lem230548 m n p h0). Qed.
Lemma lem230550 (m : nat) (n : nat) (p : nat) : term514 m n p.
Proof. exact (fun h0 : term511 p n m => @lem230536 p n m h0). Qed.
Lemma lem230551 (p : nat) (n : nat) (m : nat) : term515 p n m.
Proof. exact (conj (@lem230550 m n p) (@lem230549 p n m)). Qed.
Lemma lem230552 (m : nat) (n : nat) (p : nat) : (term515 p n m) = ((term511 p n m) = (term512 m n p)).
Proof. exact (@lem32 (term511 p n m) (term512 m n p)). Qed.
Lemma lem230553 (m : nat) (n : nat) (p : nat) : (term511 p n m) = (term512 m n p).
Proof. exact (EQ_MP (@lem230552 m n p) (@lem230551 p n m)). Qed.
Lemma lem230554 (m : nat) (n : nat) (p : nat) (h1 : (term511 p n m) = (term512 m n p)) : (term489 p n m) = (term516 m n p).
Proof. exact (@lem16917 (term489 p n m) (term516 m n p) h1). Qed.
Lemma lem230555 (m : nat) (n : nat) (p : nat) : ((term511 p n m) = (term512 m n p)) = ((term489 p n m) = (term516 m n p)).
Proof. exact (prop_ext (fun h1 : (term511 p n m) = (term512 m n p) => @lem230554 m n p h1) (fun h1 : (term489 p n m) = (term516 m n p) => @lem230553 m n p)). Qed.
Lemma lem230558 (m : nat) (n : nat) (p : nat) : (term489 p n m) = (term516 m n p).
Proof. exact (EQ_MP (@lem230555 m n p) (@lem230553 m n p)). Qed.
Lemma lem230559 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term516 m n p.
Proof. exact (EQ_MP (@lem230558 m n p) (@lem230440 n m p h1 h2 h3)). Qed.
Lemma lem230560 (m : nat) (n : nat) (h1 : term505 m n) : term505 m n.
Proof. exact (h1). Qed.
Lemma lem230561 (m : nat) (n : nat) (h1 : term505 m n) : term504 m n.
Proof. exact (@lem16684 (term490 m) (term506 m n) h1). Qed.
Lemma lem230562 (m : nat) (n : nat) (h1 : term505 m n) : (term505 m n) = (term504 m n).
Proof. exact (prop_ext (fun h2 : term505 m n => @lem230561 m n h1) (fun h2 : term504 m n => @lem230560 m n h1)). Qed.
Lemma lem230563 (m : nat) (n : nat) (h1 : term505 m n) : term504 m n.
Proof. exact (EQ_MP (@lem230562 m n h1) (@lem230560 m n h1)). Qed.
Lemma lem230564 (m : nat) (n : nat) (h1 : term505 m n) : term503 m.
Proof. exact (@lem16597 (term490 m) (term506 m n) h1). Qed.
Lemma lem230565 (m : nat) (n : nat) (h1 : term505 m n) : (term505 m n) = (term503 m).
Proof. exact (prop_ext (fun h2 : term505 m n => @lem230564 m n h1) (fun h2 : term503 m => @lem230560 m n h1)). Qed.
Lemma lem230566 (m : nat) (n : nat) (h1 : term505 m n) : term503 m.
Proof. exact (EQ_MP (@lem230565 m n h1) (@lem230560 m n h1)). Qed.
Lemma lem230567 (m : nat) (n : nat) (h1 : term504 m n) : term239 m n.
Proof. exact (@lem16684 (term501 n m) (m = (term4 m n)) h1). Qed.
Lemma lem230568 (m : nat) (n : nat) (h1 : term505 m n) : (term504 m n) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term504 m n => @lem230567 m n h2) (fun h2 : term239 m n => @lem230563 m n h1)). Qed.
Lemma lem230569 (m : nat) (n : nat) (h1 : term505 m n) : term239 m n.
Proof. exact (EQ_MP (@lem230568 m n h1) (@lem230563 m n h1)). Qed.
Lemma lem230570 (m : nat) (n : nat) (h1 : term504 m n) : term502 n m.
Proof. exact (@lem16597 (term501 n m) (m = (term4 m n)) h1). Qed.
Lemma lem230571 (m : nat) (n : nat) (h1 : term505 m n) : (term504 m n) = (term502 n m).
Proof. exact (prop_ext (fun h2 : term504 m n => @lem230570 m n h2) (fun h2 : term502 n m => @lem230563 m n h1)). Qed.
Lemma lem230572 (m : nat) (n : nat) (h1 : term505 m n) : term502 n m.
Proof. exact (EQ_MP (@lem230571 m n h1) (@lem230563 m n h1)). Qed.
Lemma lem230573 (m : nat) (n : nat) (h1 : term503 m) (h2 : term239 m n) : term517 m n.
Proof. exact (@lem16799 (term490 m) (m = (term4 m n)) h1 h2). Qed.
Lemma lem230574 (m : nat) (n : nat) (h1 : term503 m) (h2 : term505 m n) : (term239 m n) = (term517 m n).
Proof. exact (prop_ext (fun h3 : term239 m n => @lem230573 m n h1 h3) (fun h3 : term517 m n => @lem230569 m n h2)). Qed.
Lemma lem230575 (m : nat) (n : nat) (h1 : term503 m) (h2 : term505 m n) : term517 m n.
Proof. exact (EQ_MP (@lem230574 m n h1 h2) (@lem230569 m n h2)). Qed.
Lemma lem230576 (m : nat) (n : nat) (h1 : term505 m n) : (term503 m) = (term517 m n).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230575 m n h2 h1) (fun h2 : term517 m n => @lem230566 m n h1)). Qed.
Lemma lem230577 (m : nat) (n : nat) (h1 : term505 m n) : term517 m n.
Proof. exact (EQ_MP (@lem230576 m n h1) (@lem230566 m n h1)). Qed.
Lemma lem230578 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term517 m n) : term518 m n.
Proof. exact (@lem16799 (term501 n m) (term519 m n) h1 h2). Qed.
Lemma lem230579 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term505 m n) : (term517 m n) = (term518 m n).
Proof. exact (prop_ext (fun h3 : term517 m n => @lem230578 m n h1 h3) (fun h3 : term518 m n => @lem230577 m n h2)). Qed.
Lemma lem230580 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term505 m n) : term518 m n.
Proof. exact (EQ_MP (@lem230579 m n h1 h2) (@lem230577 m n h2)). Qed.
Lemma lem230581 (m : nat) (n : nat) (h1 : term505 m n) : (term502 n m) = (term518 m n).
Proof. exact (prop_ext (fun h2 : term502 n m => @lem230580 m n h2 h1) (fun h2 : term518 m n => @lem230572 m n h1)). Qed.
Lemma lem230582 (m : nat) (n : nat) (h1 : term505 m n) : term518 m n.
Proof. exact (EQ_MP (@lem230581 m n h1) (@lem230572 m n h1)). Qed.
Lemma lem230583 (m : nat) (n : nat) (h1 : term518 m n) : term518 m n.
Proof. exact (h1). Qed.
Lemma lem230584 (m : nat) (n : nat) (h1 : term518 m n) : term517 m n.
Proof. exact (@lem16684 (term501 n m) (term519 m n) h1). Qed.
Lemma lem230585 (m : nat) (n : nat) (h1 : term518 m n) : (term518 m n) = (term517 m n).
Proof. exact (prop_ext (fun h2 : term518 m n => @lem230584 m n h1) (fun h2 : term517 m n => @lem230583 m n h1)). Qed.
Lemma lem230586 (m : nat) (n : nat) (h1 : term518 m n) : term517 m n.
Proof. exact (EQ_MP (@lem230585 m n h1) (@lem230583 m n h1)). Qed.
Lemma lem230587 (m : nat) (n : nat) (h1 : term518 m n) : term502 n m.
Proof. exact (@lem16597 (term501 n m) (term519 m n) h1). Qed.
Lemma lem230588 (m : nat) (n : nat) (h1 : term518 m n) : (term518 m n) = (term502 n m).
Proof. exact (prop_ext (fun h2 : term518 m n => @lem230587 m n h1) (fun h2 : term502 n m => @lem230583 m n h1)). Qed.
Lemma lem230589 (m : nat) (n : nat) (h1 : term518 m n) : term502 n m.
Proof. exact (EQ_MP (@lem230588 m n h1) (@lem230583 m n h1)). Qed.
Lemma lem230590 (m : nat) (n : nat) (h1 : term517 m n) : term239 m n.
Proof. exact (@lem16684 (term490 m) (m = (term4 m n)) h1). Qed.
Lemma lem230591 (m : nat) (n : nat) (h1 : term518 m n) : (term517 m n) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term517 m n => @lem230590 m n h2) (fun h2 : term239 m n => @lem230586 m n h1)). Qed.
Lemma lem230592 (m : nat) (n : nat) (h1 : term518 m n) : term239 m n.
Proof. exact (EQ_MP (@lem230591 m n h1) (@lem230586 m n h1)). Qed.
Lemma lem230593 (m : nat) (n : nat) (h1 : term517 m n) : term503 m.
Proof. exact (@lem16597 (term490 m) (m = (term4 m n)) h1). Qed.
Lemma lem230594 (m : nat) (n : nat) (h1 : term518 m n) : (term517 m n) = (term503 m).
Proof. exact (prop_ext (fun h2 : term517 m n => @lem230593 m n h2) (fun h2 : term503 m => @lem230586 m n h1)). Qed.
Lemma lem230595 (m : nat) (n : nat) (h1 : term518 m n) : term503 m.
Proof. exact (EQ_MP (@lem230594 m n h1) (@lem230586 m n h1)). Qed.
Lemma lem230596 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term239 m n) : term504 m n.
Proof. exact (@lem16799 (term501 n m) (m = (term4 m n)) h1 h2). Qed.
Lemma lem230597 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term518 m n) : (term239 m n) = (term504 m n).
Proof. exact (prop_ext (fun h3 : term239 m n => @lem230596 m n h1 h3) (fun h3 : term504 m n => @lem230592 m n h2)). Qed.
Lemma lem230598 (m : nat) (n : nat) (h1 : term502 n m) (h2 : term518 m n) : term504 m n.
Proof. exact (EQ_MP (@lem230597 m n h1 h2) (@lem230592 m n h2)). Qed.
Lemma lem230599 (m : nat) (n : nat) (h1 : term518 m n) : (term502 n m) = (term504 m n).
Proof. exact (prop_ext (fun h2 : term502 n m => @lem230598 m n h2 h1) (fun h2 : term504 m n => @lem230589 m n h1)). Qed.
Lemma lem230600 (m : nat) (n : nat) (h1 : term518 m n) : term504 m n.
Proof. exact (EQ_MP (@lem230599 m n h1) (@lem230589 m n h1)). Qed.
Lemma lem230601 (m : nat) (n : nat) (h1 : term503 m) (h2 : term504 m n) : term505 m n.
Proof. exact (@lem16799 (term490 m) (term506 m n) h1 h2). Qed.
Lemma lem230602 (m : nat) (n : nat) (h1 : term503 m) (h2 : term518 m n) : (term504 m n) = (term505 m n).
Proof. exact (prop_ext (fun h3 : term504 m n => @lem230601 m n h1 h3) (fun h3 : term505 m n => @lem230600 m n h2)). Qed.
Lemma lem230603 (m : nat) (n : nat) (h1 : term503 m) (h2 : term518 m n) : term505 m n.
Proof. exact (EQ_MP (@lem230602 m n h1 h2) (@lem230600 m n h2)). Qed.
Lemma lem230604 (m : nat) (n : nat) (h1 : term518 m n) : (term503 m) = (term505 m n).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230603 m n h2 h1) (fun h2 : term505 m n => @lem230595 m n h1)). Qed.
Lemma lem230605 (m : nat) (n : nat) (h1 : term518 m n) : term505 m n.
Proof. exact (EQ_MP (@lem230604 m n h1) (@lem230595 m n h1)). Qed.
Lemma lem230606 (m : nat) (n : nat) : term520 m n.
Proof. exact (fun h0 : term518 m n => @lem230605 m n h0). Qed.
Lemma lem230607 (m : nat) (n : nat) : term521 m n.
Proof. exact (fun h0 : term505 m n => @lem230582 m n h0). Qed.
Lemma lem230608 (m : nat) (n : nat) : term522 m n.
Proof. exact (conj (@lem230607 m n) (@lem230606 m n)). Qed.
Lemma lem230609 (m : nat) (n : nat) : (term522 m n) = ((term505 m n) = (term518 m n)).
Proof. exact (@lem32 (term505 m n) (term518 m n)). Qed.
Lemma lem230610 (m : nat) (n : nat) : (term505 m n) = (term518 m n).
Proof. exact (EQ_MP (@lem230609 m n) (@lem230608 m n)). Qed.
Lemma lem230611 (m : nat) (n : nat) (h1 : (term505 m n) = (term518 m n)) : (term510 m n) = (term523 m n).
Proof. exact (@lem16917 (term510 m n) (term523 m n) h1). Qed.
Lemma lem230612 (m : nat) (n : nat) : ((term505 m n) = (term518 m n)) = ((term510 m n) = (term523 m n)).
Proof. exact (prop_ext (fun h1 : (term505 m n) = (term518 m n) => @lem230611 m n h1) (fun h1 : (term510 m n) = (term523 m n) => @lem230610 m n)). Qed.
Lemma lem230615 (m : nat) (n : nat) : (term510 m n) = (term523 m n).
Proof. exact (EQ_MP (@lem230612 m n) (@lem230610 m n)). Qed.
Lemma lem230616 (m : nat) (n : nat) : term523 m n.
Proof. exact (EQ_MP (@lem230615 m n) (@lem230524 m n)). Qed.
Lemma lem230617 (n : nat) (m : nat) : term524 n m.
Proof. exact (@lem22288 ((term4 m n) = m)). Qed.
Lemma lem230618 (n : nat) (m : nat) : (term524 n m) = (term525 n m).
Proof. exact (eq_refl (term524 n m)). Qed.
Lemma lem230619 (n : nat) (m : nat) : term525 n m.
Proof. exact (EQ_MP (@lem230618 n m) (@lem230617 n m)). Qed.
Lemma lem230620 (m : nat) (n : nat) (p : nat) : term526 m n p.
Proof. exact (@lem230619 n m (n = p)). Qed.
Lemma lem230621 (m : nat) (n : nat) (p : nat) : (term526 m n p) = (term527 m n p).
Proof. exact (eq_refl (term526 m n p)). Qed.
Lemma lem230622 (m : nat) (n : nat) (p : nat) : term527 m n p.
Proof. exact (EQ_MP (@lem230621 m n p) (@lem230620 m n p)). Qed.
Lemma lem230623 (p : nat) (m : nat) (n : nat) : term528 p m n.
Proof. exact (@lem230622 m n p (term519 m n)). Qed.
Lemma lem230624 (p : nat) (m : nat) (n : nat) : (term528 p m n) = (term529 p m n).
Proof. exact (eq_refl (term528 p m n)). Qed.
Lemma lem230625 (p : nat) (m : nat) (n : nat) : term529 p m n.
Proof. exact (EQ_MP (@lem230624 p m n) (@lem230623 p m n)). Qed.
Lemma lem230626 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term530 p m n.
Proof. exact (@lem230625 p m n (@lem230559 m n p h1 h2 h3)). Qed.
Lemma lem230627 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term531 p m n.
Proof. exact (@lem230626 m n p h1 h2 h3 (@lem230616 m n)). Qed.
Lemma lem230628 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term532 p m n.
Proof. exact (h1). Qed.
Lemma lem230629 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term517 m n.
Proof. exact (@lem16684 (n = p) (term519 m n) h1). Qed.
Lemma lem230630 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : (term532 p m n) = (term517 m n).
Proof. exact (prop_ext (fun h2 : term532 p m n => @lem230629 p m n h1) (fun h2 : term517 m n => @lem230628 p m n h1)). Qed.
Lemma lem230631 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term517 m n.
Proof. exact (EQ_MP (@lem230630 p m n h1) (@lem230628 p m n h1)). Qed.
Lemma lem230632 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term87 n p.
Proof. exact (@lem16597 (n = p) (term519 m n) h1). Qed.
Lemma lem230633 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : (term532 p m n) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term532 p m n => @lem230632 p m n h1) (fun h2 : term87 n p => @lem230628 p m n h1)). Qed.
Lemma lem230634 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term87 n p.
Proof. exact (EQ_MP (@lem230633 p m n h1) (@lem230628 p m n h1)). Qed.
Lemma lem230635 (m : nat) (n : nat) (h1 : term517 m n) : term239 m n.
Proof. exact (@lem16684 (term490 m) (m = (term4 m n)) h1). Qed.
Lemma lem230636 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : (term517 m n) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term517 m n => @lem230635 m n h2) (fun h2 : term239 m n => @lem230631 p m n h1)). Qed.
Lemma lem230637 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term239 m n.
Proof. exact (EQ_MP (@lem230636 p m n h1) (@lem230631 p m n h1)). Qed.
Lemma lem230638 (m : nat) (n : nat) (h1 : term517 m n) : term503 m.
Proof. exact (@lem16597 (term490 m) (m = (term4 m n)) h1). Qed.
Lemma lem230639 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : (term517 m n) = (term503 m).
Proof. exact (prop_ext (fun h2 : term517 m n => @lem230638 m n h2) (fun h2 : term503 m => @lem230631 p m n h1)). Qed.
Lemma lem230640 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term503 m.
Proof. exact (EQ_MP (@lem230639 p m n h1) (@lem230631 p m n h1)). Qed.
Lemma lem230641 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term87 n p) : term476 m n p.
Proof. exact (@lem16799 (m = (term4 m n)) (n = p) h1 h2). Qed.
Lemma lem230642 (p : nat) (m : nat) (n : nat) (h1 : term239 m n) (h2 : term532 p m n) : (term87 n p) = (term476 m n p).
Proof. exact (prop_ext (fun h3 : term87 n p => @lem230641 m n p h1 h3) (fun h3 : term476 m n p => @lem230634 p m n h2)). Qed.
Lemma lem230643 (p : nat) (m : nat) (n : nat) (h1 : term239 m n) (h2 : term532 p m n) : term476 m n p.
Proof. exact (EQ_MP (@lem230642 p m n h1 h2) (@lem230634 p m n h2)). Qed.
Lemma lem230644 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : (term239 m n) = (term476 m n p).
Proof. exact (prop_ext (fun h2 : term239 m n => @lem230643 p m n h2 h1) (fun h2 : term476 m n p => @lem230637 p m n h1)). Qed.
Lemma lem230645 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term476 m n p.
Proof. exact (EQ_MP (@lem230644 p m n h1) (@lem230637 p m n h1)). Qed.
Lemma lem230646 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term476 m n p) : term533 m n p.
Proof. exact (@lem16799 (term490 m) (term480 m n p) h1 h2). Qed.
Lemma lem230647 (p : nat) (m : nat) (n : nat) (h1 : term503 m) (h2 : term532 p m n) : (term476 m n p) = (term533 m n p).
Proof. exact (prop_ext (fun h3 : term476 m n p => @lem230646 m n p h1 h3) (fun h3 : term533 m n p => @lem230645 p m n h2)). Qed.
Lemma lem230648 (p : nat) (m : nat) (n : nat) (h1 : term503 m) (h2 : term532 p m n) : term533 m n p.
Proof. exact (EQ_MP (@lem230647 p m n h1 h2) (@lem230645 p m n h2)). Qed.
Lemma lem230649 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : (term503 m) = (term533 m n p).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230648 p m n h2 h1) (fun h2 : term533 m n p => @lem230640 p m n h1)). Qed.
Lemma lem230650 (p : nat) (m : nat) (n : nat) (h1 : term532 p m n) : term533 m n p.
Proof. exact (EQ_MP (@lem230649 p m n h1) (@lem230640 p m n h1)). Qed.
Lemma lem230651 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term533 m n p.
Proof. exact (h1). Qed.
Lemma lem230652 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term476 m n p.
Proof. exact (@lem16684 (term490 m) (term480 m n p) h1). Qed.
Lemma lem230653 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term533 m n p) = (term476 m n p).
Proof. exact (prop_ext (fun h2 : term533 m n p => @lem230652 m n p h1) (fun h2 : term476 m n p => @lem230651 m n p h1)). Qed.
Lemma lem230654 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term476 m n p.
Proof. exact (EQ_MP (@lem230653 m n p h1) (@lem230651 m n p h1)). Qed.
Lemma lem230655 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term503 m.
Proof. exact (@lem16597 (term490 m) (term480 m n p) h1). Qed.
Lemma lem230656 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term533 m n p) = (term503 m).
Proof. exact (prop_ext (fun h2 : term533 m n p => @lem230655 m n p h1) (fun h2 : term503 m => @lem230651 m n p h1)). Qed.
Lemma lem230657 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term503 m.
Proof. exact (EQ_MP (@lem230656 m n p h1) (@lem230651 m n p h1)). Qed.
Lemma lem230658 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term87 n p.
Proof. exact (@lem16684 (m = (term4 m n)) (n = p) h1). Qed.
Lemma lem230659 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term476 m n p) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term476 m n p => @lem230658 m n p h2) (fun h2 : term87 n p => @lem230654 m n p h1)). Qed.
Lemma lem230660 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term87 n p.
Proof. exact (EQ_MP (@lem230659 m n p h1) (@lem230654 m n p h1)). Qed.
Lemma lem230661 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term239 m n.
Proof. exact (@lem16597 (m = (term4 m n)) (n = p) h1). Qed.
Lemma lem230662 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term476 m n p) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term476 m n p => @lem230661 m n p h2) (fun h2 : term239 m n => @lem230654 m n p h1)). Qed.
Lemma lem230663 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term239 m n.
Proof. exact (EQ_MP (@lem230662 m n p h1) (@lem230654 m n p h1)). Qed.
Lemma lem230664 (m : nat) (n : nat) (h1 : term503 m) (h2 : term239 m n) : term517 m n.
Proof. exact (@lem16799 (term490 m) (m = (term4 m n)) h1 h2). Qed.
Lemma lem230665 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term533 m n p) : (term239 m n) = (term517 m n).
Proof. exact (prop_ext (fun h3 : term239 m n => @lem230664 m n h1 h3) (fun h3 : term517 m n => @lem230663 m n p h2)). Qed.
Lemma lem230666 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term533 m n p) : term517 m n.
Proof. exact (EQ_MP (@lem230665 m n p h1 h2) (@lem230663 m n p h2)). Qed.
Lemma lem230667 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term503 m) = (term517 m n).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230666 m n p h2 h1) (fun h2 : term517 m n => @lem230657 m n p h1)). Qed.
Lemma lem230668 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term517 m n.
Proof. exact (EQ_MP (@lem230667 m n p h1) (@lem230657 m n p h1)). Qed.
Lemma lem230669 (p : nat) (m : nat) (n : nat) (h1 : term87 n p) (h2 : term517 m n) : term532 p m n.
Proof. exact (@lem16799 (n = p) (term519 m n) h1 h2). Qed.
Lemma lem230670 (m : nat) (n : nat) (p : nat) (h1 : term87 n p) (h2 : term533 m n p) : (term517 m n) = (term532 p m n).
Proof. exact (prop_ext (fun h3 : term517 m n => @lem230669 p m n h1 h3) (fun h3 : term532 p m n => @lem230668 m n p h2)). Qed.
Lemma lem230671 (m : nat) (n : nat) (p : nat) (h1 : term87 n p) (h2 : term533 m n p) : term532 p m n.
Proof. exact (EQ_MP (@lem230670 m n p h1 h2) (@lem230668 m n p h2)). Qed.
Lemma lem230672 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term87 n p) = (term532 p m n).
Proof. exact (prop_ext (fun h2 : term87 n p => @lem230671 m n p h2 h1) (fun h2 : term532 p m n => @lem230660 m n p h1)). Qed.
Lemma lem230673 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term532 p m n.
Proof. exact (EQ_MP (@lem230672 m n p h1) (@lem230660 m n p h1)). Qed.
Lemma lem230674 (p : nat) (m : nat) (n : nat) : term534 p m n.
Proof. exact (fun h0 : term533 m n p => @lem230673 m n p h0). Qed.
Lemma lem230675 (m : nat) (n : nat) (p : nat) : term535 m n p.
Proof. exact (fun h0 : term532 p m n => @lem230650 p m n h0). Qed.
Lemma lem230676 (p : nat) (m : nat) (n : nat) : term536 p m n.
Proof. exact (conj (@lem230675 m n p) (@lem230674 p m n)). Qed.
Lemma lem230677 (m : nat) (n : nat) (p : nat) : (term536 p m n) = ((term532 p m n) = (term533 m n p)).
Proof. exact (@lem32 (term532 p m n) (term533 m n p)). Qed.
Lemma lem230678 (m : nat) (n : nat) (p : nat) : (term532 p m n) = (term533 m n p).
Proof. exact (EQ_MP (@lem230677 m n p) (@lem230676 p m n)). Qed.
Lemma lem230679 (m : nat) (n : nat) (p : nat) (h1 : (term532 p m n) = (term533 m n p)) : (term531 p m n) = (term537 m n p).
Proof. exact (@lem16917 (term531 p m n) (term537 m n p) h1). Qed.
Lemma lem230680 (m : nat) (n : nat) (p : nat) : ((term532 p m n) = (term533 m n p)) = ((term531 p m n) = (term537 m n p)).
Proof. exact (prop_ext (fun h1 : (term532 p m n) = (term533 m n p) => @lem230679 m n p h1) (fun h1 : (term531 p m n) = (term537 m n p) => @lem230678 m n p)). Qed.
Lemma lem230681 (m : nat) (n : nat) (p : nat) : (term531 p m n) = (term537 m n p).
Proof. exact (EQ_MP (@lem230680 m n p) (@lem230678 m n p)). Qed.
Lemma lem230682 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term537 m n p.
Proof. exact (EQ_MP (@lem230681 m n p) (@lem230627 m n p h1 h2 h3)). Qed.
Lemma lem230687 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term533 m n p.
Proof. exact (h1). Qed.
Lemma lem230688 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term476 m n p.
Proof. exact (@lem16684 (term490 m) (term480 m n p) h1). Qed.
Lemma lem230689 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term533 m n p) = (term476 m n p).
Proof. exact (prop_ext (fun h2 : term533 m n p => @lem230688 m n p h1) (fun h2 : term476 m n p => @lem230687 m n p h1)). Qed.
Lemma lem230690 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term476 m n p.
Proof. exact (EQ_MP (@lem230689 m n p h1) (@lem230687 m n p h1)). Qed.
Lemma lem230691 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term503 m.
Proof. exact (@lem16597 (term490 m) (term480 m n p) h1). Qed.
Lemma lem230692 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term533 m n p) = (term503 m).
Proof. exact (prop_ext (fun h2 : term533 m n p => @lem230691 m n p h1) (fun h2 : term503 m => @lem230687 m n p h1)). Qed.
Lemma lem230693 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term503 m.
Proof. exact (EQ_MP (@lem230692 m n p h1) (@lem230687 m n p h1)). Qed.
Lemma lem230694 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term87 n p.
Proof. exact (@lem16684 (m = (term4 m n)) (n = p) h1). Qed.
Lemma lem230695 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term476 m n p) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term476 m n p => @lem230694 m n p h2) (fun h2 : term87 n p => @lem230690 m n p h1)). Qed.
Lemma lem230696 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term87 n p.
Proof. exact (EQ_MP (@lem230695 m n p h1) (@lem230690 m n p h1)). Qed.
Lemma lem230697 (m : nat) (n : nat) (p : nat) (h1 : term476 m n p) : term239 m n.
Proof. exact (@lem16597 (m = (term4 m n)) (n = p) h1). Qed.
Lemma lem230698 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term476 m n p) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term476 m n p => @lem230697 m n p h2) (fun h2 : term239 m n => @lem230690 m n p h1)). Qed.
Lemma lem230699 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term239 m n.
Proof. exact (EQ_MP (@lem230698 m n p h1) (@lem230690 m n p h1)). Qed.
Lemma lem230700 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term87 n p) : term538 m n p.
Proof. exact (@lem16799 (term490 m) (n = p) h1 h2). Qed.
Lemma lem230701 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term533 m n p) : (term87 n p) = (term538 m n p).
Proof. exact (prop_ext (fun h3 : term87 n p => @lem230700 m n p h1 h3) (fun h3 : term538 m n p => @lem230696 m n p h2)). Qed.
Lemma lem230702 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term533 m n p) : term538 m n p.
Proof. exact (EQ_MP (@lem230701 m n p h1 h2) (@lem230696 m n p h2)). Qed.
Lemma lem230703 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term503 m) = (term538 m n p).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230702 m n p h2 h1) (fun h2 : term538 m n p => @lem230693 m n p h1)). Qed.
Lemma lem230704 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term538 m n p.
Proof. exact (EQ_MP (@lem230703 m n p h1) (@lem230693 m n p h1)). Qed.
Lemma lem230705 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term538 m n p) : term539 m n p.
Proof. exact (@lem16799 (m = (term4 m n)) (term540 m n p) h1 h2). Qed.
Lemma lem230706 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term533 m n p) : (term538 m n p) = (term539 m n p).
Proof. exact (prop_ext (fun h3 : term538 m n p => @lem230705 m n p h1 h3) (fun h3 : term539 m n p => @lem230704 m n p h2)). Qed.
Lemma lem230707 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term533 m n p) : term539 m n p.
Proof. exact (EQ_MP (@lem230706 m n p h1 h2) (@lem230704 m n p h2)). Qed.
Lemma lem230708 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : (term239 m n) = (term539 m n p).
Proof. exact (prop_ext (fun h2 : term239 m n => @lem230707 m n p h2 h1) (fun h2 : term539 m n p => @lem230699 m n p h1)). Qed.
Lemma lem230709 (m : nat) (n : nat) (p : nat) (h1 : term533 m n p) : term539 m n p.
Proof. exact (EQ_MP (@lem230708 m n p h1) (@lem230699 m n p h1)). Qed.
Lemma lem230710 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term539 m n p.
Proof. exact (h1). Qed.
Lemma lem230711 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term538 m n p.
Proof. exact (@lem16684 (m = (term4 m n)) (term540 m n p) h1). Qed.
Lemma lem230712 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : (term539 m n p) = (term538 m n p).
Proof. exact (prop_ext (fun h2 : term539 m n p => @lem230711 m n p h1) (fun h2 : term538 m n p => @lem230710 m n p h1)). Qed.
Lemma lem230713 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term538 m n p.
Proof. exact (EQ_MP (@lem230712 m n p h1) (@lem230710 m n p h1)). Qed.
Lemma lem230714 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term239 m n.
Proof. exact (@lem16597 (m = (term4 m n)) (term540 m n p) h1). Qed.
Lemma lem230715 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : (term539 m n p) = (term239 m n).
Proof. exact (prop_ext (fun h2 : term539 m n p => @lem230714 m n p h1) (fun h2 : term239 m n => @lem230710 m n p h1)). Qed.
Lemma lem230716 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term239 m n.
Proof. exact (EQ_MP (@lem230715 m n p h1) (@lem230710 m n p h1)). Qed.
Lemma lem230717 (m : nat) (n : nat) (p : nat) (h1 : term538 m n p) : term87 n p.
Proof. exact (@lem16684 (term490 m) (n = p) h1). Qed.
Lemma lem230718 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : (term538 m n p) = (term87 n p).
Proof. exact (prop_ext (fun h2 : term538 m n p => @lem230717 m n p h2) (fun h2 : term87 n p => @lem230713 m n p h1)). Qed.
Lemma lem230719 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term87 n p.
Proof. exact (EQ_MP (@lem230718 m n p h1) (@lem230713 m n p h1)). Qed.
Lemma lem230720 (m : nat) (n : nat) (p : nat) (h1 : term538 m n p) : term503 m.
Proof. exact (@lem16597 (term490 m) (n = p) h1). Qed.
Lemma lem230721 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : (term538 m n p) = (term503 m).
Proof. exact (prop_ext (fun h2 : term538 m n p => @lem230720 m n p h2) (fun h2 : term503 m => @lem230713 m n p h1)). Qed.
Lemma lem230722 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term503 m.
Proof. exact (EQ_MP (@lem230721 m n p h1) (@lem230713 m n p h1)). Qed.
Lemma lem230723 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term87 n p) : term476 m n p.
Proof. exact (@lem16799 (m = (term4 m n)) (n = p) h1 h2). Qed.
Lemma lem230724 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term539 m n p) : (term87 n p) = (term476 m n p).
Proof. exact (prop_ext (fun h3 : term87 n p => @lem230723 m n p h1 h3) (fun h3 : term476 m n p => @lem230719 m n p h2)). Qed.
Lemma lem230725 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term539 m n p) : term476 m n p.
Proof. exact (EQ_MP (@lem230724 m n p h1 h2) (@lem230719 m n p h2)). Qed.
Lemma lem230726 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : (term239 m n) = (term476 m n p).
Proof. exact (prop_ext (fun h2 : term239 m n => @lem230725 m n p h2 h1) (fun h2 : term476 m n p => @lem230716 m n p h1)). Qed.
Lemma lem230727 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term476 m n p.
Proof. exact (EQ_MP (@lem230726 m n p h1) (@lem230716 m n p h1)). Qed.
Lemma lem230728 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term476 m n p) : term533 m n p.
Proof. exact (@lem16799 (term490 m) (term480 m n p) h1 h2). Qed.
Lemma lem230729 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term539 m n p) : (term476 m n p) = (term533 m n p).
Proof. exact (prop_ext (fun h3 : term476 m n p => @lem230728 m n p h1 h3) (fun h3 : term533 m n p => @lem230727 m n p h2)). Qed.
Lemma lem230730 (m : nat) (n : nat) (p : nat) (h1 : term503 m) (h2 : term539 m n p) : term533 m n p.
Proof. exact (EQ_MP (@lem230729 m n p h1 h2) (@lem230727 m n p h2)). Qed.
Lemma lem230731 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : (term503 m) = (term533 m n p).
Proof. exact (prop_ext (fun h2 : term503 m => @lem230730 m n p h2 h1) (fun h2 : term533 m n p => @lem230722 m n p h1)). Qed.
Lemma lem230732 (m : nat) (n : nat) (p : nat) (h1 : term539 m n p) : term533 m n p.
Proof. exact (EQ_MP (@lem230731 m n p h1) (@lem230722 m n p h1)). Qed.
Lemma lem230733 (m : nat) (n : nat) (p : nat) : term541 m n p.
Proof. exact (fun h0 : term539 m n p => @lem230732 m n p h0). Qed.
Lemma lem230734 (m : nat) (n : nat) (p : nat) : term542 m n p.
Proof. exact (fun h0 : term533 m n p => @lem230709 m n p h0). Qed.
Lemma lem230735 (m : nat) (n : nat) (p : nat) : term543 m n p.
Proof. exact (conj (@lem230734 m n p) (@lem230733 m n p)). Qed.
Lemma lem230736 (m : nat) (n : nat) (p : nat) : (term543 m n p) = ((term533 m n p) = (term539 m n p)).
Proof. exact (@lem32 (term533 m n p) (term539 m n p)). Qed.
Lemma lem230737 (m : nat) (n : nat) (p : nat) : (term533 m n p) = (term539 m n p).
Proof. exact (EQ_MP (@lem230736 m n p) (@lem230735 m n p)). Qed.
Lemma lem230738 (m : nat) (n : nat) (p : nat) (h1 : (term533 m n p) = (term539 m n p)) : (term537 m n p) = (term544 m n p).
Proof. exact (@lem16917 (term537 m n p) (term544 m n p) h1). Qed.
Lemma lem230739 (m : nat) (n : nat) (p : nat) : ((term533 m n p) = (term539 m n p)) = ((term537 m n p) = (term544 m n p)).
Proof. exact (prop_ext (fun h1 : (term533 m n p) = (term539 m n p) => @lem230738 m n p h1) (fun h1 : (term537 m n p) = (term544 m n p) => @lem230737 m n p)). Qed.
Lemma lem230742 (m : nat) (n : nat) (p : nat) : (term537 m n p) = (term544 m n p).
Proof. exact (EQ_MP (@lem230739 m n p) (@lem230737 m n p)). Qed.
Lemma lem230743 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term544 m n p.
Proof. exact (EQ_MP (@lem230742 m n p) (@lem230682 m n p h1 h2 h3)). Qed.
Lemma lem230747 (m : nat) (n : nat) (h1 : term239 m n) : term239 m n.
Proof. exact (h1). Qed.
Lemma lem230748 (m : nat) (n : nat) : term545 m n.
Proof. exact (@lem21930 (m = (term4 m n))). Qed.
Lemma lem230749 (m : nat) (n : nat) : (term545 m n) = (term546 m n).
Proof. exact (eq_refl (term545 m n)). Qed.
Lemma lem230750 (m : nat) (n : nat) : term546 m n.
Proof. exact (EQ_MP (@lem230749 m n) (@lem230748 m n)). Qed.
Lemma lem230751 (m : nat) (n : nat) (p : nat) : term547 m n p.
Proof. exact (@lem230750 m n (term540 m n p)). Qed.
Lemma lem230752 (m : nat) (n : nat) (p : nat) : (term547 m n p) = (term548 m n p).
Proof. exact (eq_refl (term547 m n p)). Qed.
Lemma lem230753 (m : nat) (n : nat) (p : nat) : term548 m n p.
Proof. exact (EQ_MP (@lem230752 m n p) (@lem230751 m n p)). Qed.
Lemma lem230754 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : p = (NUMERAL 0)) : term549 m n p.
Proof. exact (@lem230753 m n p (@lem230743 m n p h1 h2 h3)). Qed.
Lemma lem230761 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem230765 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : p = (NUMERAL 0)) : term540 m n p.
Proof. exact (@lem230754 m n p h1 h2 h4 (@lem230747 m n h3)). Qed.
Lemma lem230766 (m : nat) : term550 m.
Proof. exact (@lem22025 (m = m)). Qed.
Lemma lem230767 (m : nat) : (term550 m) = (term551 m).
Proof. exact (eq_refl (term550 m)). Qed.
Lemma lem230768 (m : nat) : term551 m.
Proof. exact (EQ_MP (@lem230767 m) (@lem230766 m)). Qed.
Lemma lem230769 (m : nat) (n : nat) (p : nat) : term552 m n p.
Proof. exact (@lem230768 m (n = p)). Qed.
Lemma lem230770 (m : nat) (n : nat) (p : nat) : (term552 m n p) = (term553 m n p).
Proof. exact (eq_refl (term552 m n p)). Qed.
Lemma lem230771 (m : nat) (n : nat) (p : nat) : term553 m n p.
Proof. exact (EQ_MP (@lem230770 m n p) (@lem230769 m n p)). Qed.
Lemma lem230772 (m : nat) (n : nat) (p : nat) : term554 m n p.
Proof. exact (@lem230771 m n p (@lem230761 m)). Qed.
Lemma lem230780 {_13143 : Type'} (__x : _13143) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem230782 {_13145 : Type'} (__x : _13145) (h1 : __x = __x) : __x = __x.
Proof. exact (h1). Qed.
Lemma lem230784 {_13145 : Type'} (__x : _13145) (__y : _13145) (h1 : __x = __y) : __x = __y.
Proof. exact (h1). Qed.
Lemma lem230785 {_13145 : Type'} : (@eq _13145) = (@eq _13145).
Proof. exact (eq_refl (@eq _13145)). Qed.
Lemma lem230786 {_13145 : Type'} (__x : _13145) (__y : _13145) (h1 : __x = __y) : (@eq _13145 __x) = (@eq _13145 __y).
Proof. exact (MK_COMB (@lem230785 _13145) (@lem230784 _13145 __x __y h1)). Qed.
Lemma lem230787 {_13145 : Type'} (__x : _13145) : __x = __x.
Proof. exact (eq_refl __x). Qed.
Lemma lem230788 {_13145 : Type'} (__x : _13145) (__y : _13145) (h1 : __x = __y) : (__x = __x) = (__y = __x).
Proof. exact (MK_COMB (@lem230786 _13145 __x __y h1) (@lem230787 _13145 __x)). Qed.
Lemma lem230789 {_13145 : Type'} (__x : _13145) (__y : _13145) (h1 : __x = __x) (h2 : __x = __y) : __y = __x.
Proof. exact (EQ_MP (@lem230788 _13145 __x __y h2) (@lem230782 _13145 __x h1)). Qed.
Lemma lem230790 {_13145 : Type'} (__x : _13145) (__y : _13145) (h1 : __x = __y) : term307 _13145 __y __x.
Proof. exact (fun h0 : __x = __x => @lem230789 _13145 __x __y h0 h1). Qed.
Lemma lem230791 {_13145 : Type'} (__x : _13145) : term308 _13145 __x.
Proof. exact (@lem22518 (__x = __x)). Qed.
Lemma lem230792 {_13145 : Type'} (__x : _13145) : (term308 _13145 __x) = (term309 _13145 __x).
Proof. exact (eq_refl (term308 _13145 __x)). Qed.
Lemma lem230793 {_13145 : Type'} (__x : _13145) : term309 _13145 __x.
Proof. exact (EQ_MP (@lem230792 _13145 __x) (@lem230791 _13145 __x)). Qed.
Lemma lem230794 {_13145 : Type'} (__y : _13145) (__x : _13145) : term310 _13145 __y __x.
Proof. exact (@lem230793 _13145 __x (__y = __x)). Qed.
Lemma lem230795 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term310 _13145 __y __x) = ((term307 _13145 __y __x) = (term311 _13145 __y __x)).
Proof. exact (eq_refl (term310 _13145 __y __x)). Qed.
Lemma lem230798 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term307 _13145 __y __x) = (term311 _13145 __y __x).
Proof. exact (EQ_MP (@lem230795 _13145 __y __x) (@lem230794 _13145 __y __x)). Qed.
Lemma lem230799 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term307 _13145 __y __x) = (term311 _13145 __y __x).
Proof. exact (@lem230798 _13145 __y __x). Qed.
Lemma lem230800 {_13145 : Type'} (__x : _13145) (__y : _13145) (h1 : __x = __y) : term311 _13145 __y __x.
Proof. exact (EQ_MP (@lem230799 _13145 __y __x) (@lem230790 _13145 __x __y h1)). Qed.
Lemma lem230801 {_13145 : Type'} (__y : _13145) (__x : _13145) : term312 _13145 __y __x.
Proof. exact (fun h0 : __x = __y => @lem230800 _13145 __x __y h0). Qed.
Lemma lem230802 {_13145 : Type'} (__x : _13145) (__y : _13145) : term313 _13145 __x __y.
Proof. exact (@lem22518 (__x = __y)). Qed.
Lemma lem230803 {_13145 : Type'} (__x : _13145) (__y : _13145) : (term313 _13145 __x __y) = (term314 _13145 __x __y).
Proof. exact (eq_refl (term313 _13145 __x __y)). Qed.
Lemma lem230804 {_13145 : Type'} (__x : _13145) (__y : _13145) : term314 _13145 __x __y.
Proof. exact (EQ_MP (@lem230803 _13145 __x __y) (@lem230802 _13145 __x __y)). Qed.
Lemma lem230805 {_13145 : Type'} (__y : _13145) (__x : _13145) : term315 _13145 __y __x.
Proof. exact (@lem230804 _13145 __x __y (term311 _13145 __y __x)). Qed.
Lemma lem230806 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term315 _13145 __y __x) = ((term312 _13145 __y __x) = (term316 _13145 __y __x)).
Proof. exact (eq_refl (term315 _13145 __y __x)). Qed.
Lemma lem230809 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term312 _13145 __y __x) = (term316 _13145 __y __x).
Proof. exact (EQ_MP (@lem230806 _13145 __y __x) (@lem230805 _13145 __y __x)). Qed.
Lemma lem230810 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term312 _13145 __y __x) = (term316 _13145 __y __x).
Proof. exact (@lem230809 _13145 __y __x). Qed.
Lemma lem230811 {_13145 : Type'} (__y : _13145) (__x : _13145) : term316 _13145 __y __x.
Proof. exact (EQ_MP (@lem230810 _13145 __y __x) (@lem230801 _13145 __y __x)). Qed.
Lemma lem230812 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term317 _13145 __y __x.
Proof. exact (h1). Qed.
Lemma lem230813 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term318 _13145 __y __x.
Proof. exact (@lem16684 (term319 _13145 __x __y) (term311 _13145 __y __x) h1). Qed.
Lemma lem230814 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : (term317 _13145 __y __x) = (term318 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term317 _13145 __y __x => @lem230813 _13145 __y __x h1) (fun h2 : term318 _13145 __y __x => @lem230812 _13145 __y __x h1)). Qed.
Lemma lem230815 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term318 _13145 __y __x.
Proof. exact (EQ_MP (@lem230814 _13145 __y __x h1) (@lem230812 _13145 __y __x h1)). Qed.
Lemma lem230816 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term320 _13145 __x __y.
Proof. exact (@lem16597 (term319 _13145 __x __y) (term311 _13145 __y __x) h1). Qed.
Lemma lem230817 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : (term317 _13145 __y __x) = (term320 _13145 __x __y).
Proof. exact (prop_ext (fun h2 : term317 _13145 __y __x => @lem230816 _13145 __y __x h1) (fun h2 : term320 _13145 __x __y => @lem230812 _13145 __y __x h1)). Qed.
Lemma lem230818 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term320 _13145 __x __y.
Proof. exact (EQ_MP (@lem230817 _13145 __y __x h1) (@lem230812 _13145 __y __x h1)). Qed.
Lemma lem230819 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term318 _13145 __y __x) : term319 _13145 __y __x.
Proof. exact (@lem16684 (term321 _13145 __x) (__y = __x) h1). Qed.
Lemma lem230820 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : (term318 _13145 __y __x) = (term319 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term318 _13145 __y __x => @lem230819 _13145 __y __x h2) (fun h2 : term319 _13145 __y __x => @lem230815 _13145 __y __x h1)). Qed.
Lemma lem230821 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term319 _13145 __y __x.
Proof. exact (EQ_MP (@lem230820 _13145 __y __x h1) (@lem230815 _13145 __y __x h1)). Qed.
Lemma lem230822 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term318 _13145 __y __x) : term322 _13145 __x.
Proof. exact (@lem16597 (term321 _13145 __x) (__y = __x) h1). Qed.
Lemma lem230823 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : (term318 _13145 __y __x) = (term322 _13145 __x).
Proof. exact (prop_ext (fun h2 : term318 _13145 __y __x => @lem230822 _13145 __y __x h2) (fun h2 : term322 _13145 __x => @lem230815 _13145 __y __x h1)). Qed.
Lemma lem230824 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term322 _13145 __x.
Proof. exact (EQ_MP (@lem230823 _13145 __y __x h1) (@lem230815 _13145 __y __x h1)). Qed.
Lemma lem230825 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term320 _13145 __x __y) (h2 : term319 _13145 __y __x) : term323 _13145 __y __x.
Proof. exact (@lem16799 (term319 _13145 __x __y) (__y = __x) h1 h2). Qed.
Lemma lem230826 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term320 _13145 __x __y) (h2 : term317 _13145 __y __x) : (term319 _13145 __y __x) = (term323 _13145 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _13145 __y __x => @lem230825 _13145 __y __x h1 h3) (fun h3 : term323 _13145 __y __x => @lem230821 _13145 __y __x h2)). Qed.
Lemma lem230827 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term320 _13145 __x __y) (h2 : term317 _13145 __y __x) : term323 _13145 __y __x.
Proof. exact (EQ_MP (@lem230826 _13145 __y __x h1 h2) (@lem230821 _13145 __y __x h2)). Qed.
Lemma lem230828 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : (term320 _13145 __x __y) = (term323 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _13145 __x __y => @lem230827 _13145 __y __x h2 h1) (fun h2 : term323 _13145 __y __x => @lem230818 _13145 __y __x h1)). Qed.
Lemma lem230829 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term323 _13145 __y __x.
Proof. exact (EQ_MP (@lem230828 _13145 __y __x h1) (@lem230818 _13145 __y __x h1)). Qed.
Lemma lem230830 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term322 _13145 __x) (h2 : term323 _13145 __y __x) : term324 _13145 __y __x.
Proof. exact (@lem16799 (term321 _13145 __x) (term325 _13145 __y __x) h1 h2). Qed.
Lemma lem230831 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term322 _13145 __x) (h2 : term317 _13145 __y __x) : (term323 _13145 __y __x) = (term324 _13145 __y __x).
Proof. exact (prop_ext (fun h3 : term323 _13145 __y __x => @lem230830 _13145 __y __x h1 h3) (fun h3 : term324 _13145 __y __x => @lem230829 _13145 __y __x h2)). Qed.
Lemma lem230832 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term322 _13145 __x) (h2 : term317 _13145 __y __x) : term324 _13145 __y __x.
Proof. exact (EQ_MP (@lem230831 _13145 __y __x h1 h2) (@lem230829 _13145 __y __x h2)). Qed.
Lemma lem230833 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : (term322 _13145 __x) = (term324 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _13145 __x => @lem230832 _13145 __y __x h2 h1) (fun h2 : term324 _13145 __y __x => @lem230824 _13145 __y __x h1)). Qed.
Lemma lem230834 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term317 _13145 __y __x) : term324 _13145 __y __x.
Proof. exact (EQ_MP (@lem230833 _13145 __y __x h1) (@lem230824 _13145 __y __x h1)). Qed.
Lemma lem230835 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term324 _13145 __y __x.
Proof. exact (h1). Qed.
Lemma lem230836 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term323 _13145 __y __x.
Proof. exact (@lem16684 (term321 _13145 __x) (term325 _13145 __y __x) h1). Qed.
Lemma lem230837 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : (term324 _13145 __y __x) = (term323 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term324 _13145 __y __x => @lem230836 _13145 __y __x h1) (fun h2 : term323 _13145 __y __x => @lem230835 _13145 __y __x h1)). Qed.
Lemma lem230838 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term323 _13145 __y __x.
Proof. exact (EQ_MP (@lem230837 _13145 __y __x h1) (@lem230835 _13145 __y __x h1)). Qed.
Lemma lem230839 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term322 _13145 __x.
Proof. exact (@lem16597 (term321 _13145 __x) (term325 _13145 __y __x) h1). Qed.
Lemma lem230840 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : (term324 _13145 __y __x) = (term322 _13145 __x).
Proof. exact (prop_ext (fun h2 : term324 _13145 __y __x => @lem230839 _13145 __y __x h1) (fun h2 : term322 _13145 __x => @lem230835 _13145 __y __x h1)). Qed.
Lemma lem230841 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term322 _13145 __x.
Proof. exact (EQ_MP (@lem230840 _13145 __y __x h1) (@lem230835 _13145 __y __x h1)). Qed.
Lemma lem230842 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term323 _13145 __y __x) : term319 _13145 __y __x.
Proof. exact (@lem16684 (term319 _13145 __x __y) (__y = __x) h1). Qed.
Lemma lem230843 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : (term323 _13145 __y __x) = (term319 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term323 _13145 __y __x => @lem230842 _13145 __y __x h2) (fun h2 : term319 _13145 __y __x => @lem230838 _13145 __y __x h1)). Qed.
Lemma lem230844 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term319 _13145 __y __x.
Proof. exact (EQ_MP (@lem230843 _13145 __y __x h1) (@lem230838 _13145 __y __x h1)). Qed.
Lemma lem230845 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term323 _13145 __y __x) : term320 _13145 __x __y.
Proof. exact (@lem16597 (term319 _13145 __x __y) (__y = __x) h1). Qed.
Lemma lem230846 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : (term323 _13145 __y __x) = (term320 _13145 __x __y).
Proof. exact (prop_ext (fun h2 : term323 _13145 __y __x => @lem230845 _13145 __y __x h2) (fun h2 : term320 _13145 __x __y => @lem230838 _13145 __y __x h1)). Qed.
Lemma lem230847 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term320 _13145 __x __y.
Proof. exact (EQ_MP (@lem230846 _13145 __y __x h1) (@lem230838 _13145 __y __x h1)). Qed.
Lemma lem230848 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term322 _13145 __x) (h2 : term319 _13145 __y __x) : term318 _13145 __y __x.
Proof. exact (@lem16799 (term321 _13145 __x) (__y = __x) h1 h2). Qed.
Lemma lem230849 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term322 _13145 __x) (h2 : term324 _13145 __y __x) : (term319 _13145 __y __x) = (term318 _13145 __y __x).
Proof. exact (prop_ext (fun h3 : term319 _13145 __y __x => @lem230848 _13145 __y __x h1 h3) (fun h3 : term318 _13145 __y __x => @lem230844 _13145 __y __x h2)). Qed.
Lemma lem230850 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term322 _13145 __x) (h2 : term324 _13145 __y __x) : term318 _13145 __y __x.
Proof. exact (EQ_MP (@lem230849 _13145 __y __x h1 h2) (@lem230844 _13145 __y __x h2)). Qed.
Lemma lem230851 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : (term322 _13145 __x) = (term318 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term322 _13145 __x => @lem230850 _13145 __y __x h2 h1) (fun h2 : term318 _13145 __y __x => @lem230841 _13145 __y __x h1)). Qed.
Lemma lem230852 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term318 _13145 __y __x.
Proof. exact (EQ_MP (@lem230851 _13145 __y __x h1) (@lem230841 _13145 __y __x h1)). Qed.
Lemma lem230853 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term320 _13145 __x __y) (h2 : term318 _13145 __y __x) : term317 _13145 __y __x.
Proof. exact (@lem16799 (term319 _13145 __x __y) (term311 _13145 __y __x) h1 h2). Qed.
Lemma lem230854 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term320 _13145 __x __y) (h2 : term324 _13145 __y __x) : (term318 _13145 __y __x) = (term317 _13145 __y __x).
Proof. exact (prop_ext (fun h3 : term318 _13145 __y __x => @lem230853 _13145 __y __x h1 h3) (fun h3 : term317 _13145 __y __x => @lem230852 _13145 __y __x h2)). Qed.
Lemma lem230855 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term320 _13145 __x __y) (h2 : term324 _13145 __y __x) : term317 _13145 __y __x.
Proof. exact (EQ_MP (@lem230854 _13145 __y __x h1 h2) (@lem230852 _13145 __y __x h2)). Qed.
Lemma lem230856 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : (term320 _13145 __x __y) = (term317 _13145 __y __x).
Proof. exact (prop_ext (fun h2 : term320 _13145 __x __y => @lem230855 _13145 __y __x h2 h1) (fun h2 : term317 _13145 __y __x => @lem230847 _13145 __y __x h1)). Qed.
Lemma lem230857 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : term324 _13145 __y __x) : term317 _13145 __y __x.
Proof. exact (EQ_MP (@lem230856 _13145 __y __x h1) (@lem230847 _13145 __y __x h1)). Qed.
Lemma lem230858 {_13145 : Type'} (__y : _13145) (__x : _13145) : term326 _13145 __y __x.
Proof. exact (fun h0 : term324 _13145 __y __x => @lem230857 _13145 __y __x h0). Qed.
Lemma lem230859 {_13145 : Type'} (__y : _13145) (__x : _13145) : term327 _13145 __y __x.
Proof. exact (fun h0 : term317 _13145 __y __x => @lem230834 _13145 __y __x h0). Qed.
Lemma lem230860 {_13145 : Type'} (__y : _13145) (__x : _13145) : term328 _13145 __y __x.
Proof. exact (conj (@lem230859 _13145 __y __x) (@lem230858 _13145 __y __x)). Qed.
Lemma lem230861 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term328 _13145 __y __x) = ((term317 _13145 __y __x) = (term324 _13145 __y __x)).
Proof. exact (@lem32 (term317 _13145 __y __x) (term324 _13145 __y __x)). Qed.
Lemma lem230862 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term317 _13145 __y __x) = (term324 _13145 __y __x).
Proof. exact (EQ_MP (@lem230861 _13145 __y __x) (@lem230860 _13145 __y __x)). Qed.
Lemma lem230863 {_13145 : Type'} (__y : _13145) (__x : _13145) (h1 : (term317 _13145 __y __x) = (term324 _13145 __y __x)) : (term316 _13145 __y __x) = (term329 _13145 __y __x).
Proof. exact (@lem16917 (term316 _13145 __y __x) (term329 _13145 __y __x) h1). Qed.
Lemma lem230864 {_13145 : Type'} (__y : _13145) (__x : _13145) : ((term317 _13145 __y __x) = (term324 _13145 __y __x)) = ((term316 _13145 __y __x) = (term329 _13145 __y __x)).
Proof. exact (prop_ext (fun h1 : (term317 _13145 __y __x) = (term324 _13145 __y __x) => @lem230863 _13145 __y __x h1) (fun h1 : (term316 _13145 __y __x) = (term329 _13145 __y __x) => @lem230862 _13145 __y __x)). Qed.
Lemma lem230865 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term316 _13145 __y __x) = (term329 _13145 __y __x).
Proof. exact (EQ_MP (@lem230864 _13145 __y __x) (@lem230862 _13145 __y __x)). Qed.
Lemma lem230866 {_13145 : Type'} (__y : _13145) (__x : _13145) : term329 _13145 __y __x.
Proof. exact (EQ_MP (@lem230865 _13145 __y __x) (@lem230811 _13145 __y __x)). Qed.
Lemma lem230867 {_13145 : Type'} (__y : _13145) (__x : _13145) : term329 _13145 __y __x.
Proof. exact (@lem230866 _13145 __y __x). Qed.
Lemma lem230868 {_13145 : Type'} (__x : _13145) : __x = __x.
Proof. exact (@lem230780 _13145 __x). Qed.
Lemma lem230871 {_13145 : Type'} (__x : _13145) : (__x = __x) = (__x = __x).
Proof. exact (eq_refl (__x = __x)). Qed.
Lemma lem230872 {_13145 : Type'} (__x : _13145) : (__x = __x) = (__x = __x).
Proof. exact (@lem230871 _13145 __x). Qed.
Lemma lem230873 {_13145 : Type'} (__x : _13145) : __x = __x.
Proof. exact (EQ_MP (@lem230872 _13145 __x) (@lem230868 _13145 __x)). Qed.
Lemma lem230876 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term329 _13145 __y __x) = (term329 _13145 __y __x).
Proof. exact (eq_refl (term329 _13145 __y __x)). Qed.
Lemma lem230877 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term329 _13145 __y __x) = (term329 _13145 __y __x).
Proof. exact (@lem230876 _13145 __y __x). Qed.
Lemma lem230878 {_13145 : Type'} (__y : _13145) (__x : _13145) : term329 _13145 __y __x.
Proof. exact (EQ_MP (@lem230877 _13145 __y __x) (@lem230867 _13145 __y __x)). Qed.
Lemma lem230879 {_13145 : Type'} (__x : _13145) : term330 _13145 __x.
Proof. exact (@lem22025 (__x = __x)). Qed.
Lemma lem230880 {_13145 : Type'} (__x : _13145) : (term330 _13145 __x) = (term331 _13145 __x).
Proof. exact (eq_refl (term330 _13145 __x)). Qed.
Lemma lem230881 {_13145 : Type'} (__x : _13145) : term331 _13145 __x.
Proof. exact (EQ_MP (@lem230880 _13145 __x) (@lem230879 _13145 __x)). Qed.
Lemma lem230882 {_13145 : Type'} (__y : _13145) (__x : _13145) : term332 _13145 __y __x.
Proof. exact (@lem230881 _13145 __x (term325 _13145 __y __x)). Qed.
Lemma lem230883 {_13145 : Type'} (__y : _13145) (__x : _13145) : (term332 _13145 __y __x) = (term333 _13145 __y __x).
Proof. exact (eq_refl (term332 _13145 __y __x)). Qed.
Lemma lem230884 {_13145 : Type'} (__y : _13145) (__x : _13145) : term333 _13145 __y __x.
Proof. exact (EQ_MP (@lem230883 _13145 __y __x) (@lem230882 _13145 __y __x)). Qed.
Lemma lem230885 {_13145 : Type'} (__y : _13145) (__x : _13145) : term334 _13145 __y __x.
Proof. exact (@lem230884 _13145 __y __x (@lem230873 _13145 __x)). Qed.
Lemma lem230888 {_13145 : Type'} (__y : _13145) (__x : _13145) : term325 _13145 __y __x.
Proof. exact (@lem230885 _13145 __y __x (@lem230878 _13145 __y __x)). Qed.
Lemma lem230889 (__y : nat) (__x : nat) : term335 __y __x.
Proof. exact (@lem230888 nat __y __x). Qed.
Lemma lem230896 (p : nat) (h1 : p = (NUMERAL 0)) : p = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem230900 (p : nat) : term336 p.
Proof. exact (@lem230889 (NUMERAL 0) p). Qed.
Lemma lem230901 (p : nat) : term337 p.
Proof. exact (@lem22025 (p = (NUMERAL 0))). Qed.
Lemma lem230902 (p : nat) : (term337 p) = (term338 p).
Proof. exact (eq_refl (term337 p)). Qed.
Lemma lem230903 (p : nat) : term338 p.
Proof. exact (EQ_MP (@lem230902 p) (@lem230901 p)). Qed.
Lemma lem230904 (p : nat) : term339 p.
Proof. exact (@lem230903 p ((NUMERAL 0) = p)). Qed.
Lemma lem230905 (p : nat) : (term339 p) = (term340 p).
Proof. exact (eq_refl (term339 p)). Qed.
Lemma lem230906 (p : nat) : term340 p.
Proof. exact (EQ_MP (@lem230905 p) (@lem230904 p)). Qed.
Lemma lem230907 (p : nat) (h1 : p = (NUMERAL 0)) : term341 p.
Proof. exact (@lem230906 p (@lem230896 p h1)). Qed.
Lemma lem230914 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem230916 (p : nat) (h1 : (NUMERAL 0) = p) : (NUMERAL 0) = p.
Proof. exact (h1). Qed.
Lemma lem230917 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem230918 (n : nat) (p : nat) (h1 : (NUMERAL 0) = p) : (n = (NUMERAL 0)) = (n = p).
Proof. exact (MK_COMB (@lem230917 n) (@lem230916 p h1)). Qed.
Lemma lem230919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem230920 (n : nat) (p : nat) (h1 : (NUMERAL 0) = p) : (term209 n) = (term87 n p).
Proof. exact (MK_COMB (@lem230919) (@lem230918 n p h1)). Qed.
Lemma lem230921 (n : nat) (p : nat) (h1 : term209 n) (h2 : (NUMERAL 0) = p) : term87 n p.
Proof. exact (EQ_MP (@lem230920 n p h2) (@lem230914 n h1)). Qed.
Lemma lem230922 (n : nat) (p : nat) (h1 : (NUMERAL 0) = p) : term555 n p.
Proof. exact (fun h0 : term209 n => @lem230921 n p h0 h1). Qed.
Lemma lem230923 (n : nat) : term556 n.
Proof. exact (@lem22403 (n = (NUMERAL 0))). Qed.
Lemma lem230924 (n : nat) : (term556 n) = (term557 n).
Proof. exact (eq_refl (term556 n)). Qed.
Lemma lem230925 (n : nat) : term557 n.
Proof. exact (EQ_MP (@lem230924 n) (@lem230923 n)). Qed.
Lemma lem230926 (n : nat) (p : nat) : term558 n p.
Proof. exact (@lem230925 n (term87 n p)). Qed.
Lemma lem230927 (n : nat) (p : nat) : (term558 n p) = ((term555 n p) = (term559 n p)).
Proof. exact (eq_refl (term558 n p)). Qed.
Lemma lem230930 (n : nat) (p : nat) : (term555 n p) = (term559 n p).
Proof. exact (EQ_MP (@lem230927 n p) (@lem230926 n p)). Qed.
Lemma lem230931 (n : nat) (p : nat) (h1 : (NUMERAL 0) = p) : term559 n p.
Proof. exact (EQ_MP (@lem230930 n p) (@lem230922 n p h1)). Qed.
Lemma lem230932 (n : nat) (p : nat) : term560 n p.
Proof. exact (fun h0 : (NUMERAL 0) = p => @lem230931 n p h0). Qed.
Lemma lem230933 (p : nat) : term561 p.
Proof. exact (@lem22518 ((NUMERAL 0) = p)). Qed.
Lemma lem230934 (p : nat) : (term561 p) = (term562 p).
Proof. exact (eq_refl (term561 p)). Qed.
Lemma lem230935 (p : nat) : term562 p.
Proof. exact (EQ_MP (@lem230934 p) (@lem230933 p)). Qed.
Lemma lem230936 (n : nat) (p : nat) : term563 n p.
Proof. exact (@lem230935 p (term559 n p)). Qed.
Lemma lem230937 (n : nat) (p : nat) : (term563 n p) = ((term560 n p) = (term564 n p)).
Proof. exact (eq_refl (term563 n p)). Qed.
Lemma lem230940 (n : nat) (p : nat) : (term560 n p) = (term564 n p).
Proof. exact (EQ_MP (@lem230937 n p) (@lem230936 n p)). Qed.
Lemma lem230941 (n : nat) (p : nat) : term564 n p.
Proof. exact (EQ_MP (@lem230940 n p) (@lem230932 n p)). Qed.
Lemma lem230942 (n : nat) (p : nat) (h1 : term565 n p) : term565 n p.
Proof. exact (h1). Qed.
Lemma lem230943 (n : nat) (p : nat) (h1 : term565 n p) : term566 n p.
Proof. exact (@lem16684 (term343 p) (term559 n p) h1). Qed.
Lemma lem230944 (n : nat) (p : nat) (h1 : term565 n p) : (term565 n p) = (term566 n p).
Proof. exact (prop_ext (fun h2 : term565 n p => @lem230943 n p h1) (fun h2 : term566 n p => @lem230942 n p h1)). Qed.
Lemma lem230945 (n : nat) (p : nat) (h1 : term565 n p) : term566 n p.
Proof. exact (EQ_MP (@lem230944 n p h1) (@lem230942 n p h1)). Qed.
Lemma lem230946 (n : nat) (p : nat) (h1 : term565 n p) : term356 p.
Proof. exact (@lem16597 (term343 p) (term559 n p) h1). Qed.
Lemma lem230947 (n : nat) (p : nat) (h1 : term565 n p) : (term565 n p) = (term356 p).
Proof. exact (prop_ext (fun h2 : term565 n p => @lem230946 n p h1) (fun h2 : term356 p => @lem230942 n p h1)). Qed.
Lemma lem230948 (n : nat) (p : nat) (h1 : term565 n p) : term356 p.
Proof. exact (EQ_MP (@lem230947 n p h1) (@lem230942 n p h1)). Qed.
Lemma lem230949 (n : nat) (p : nat) (h1 : term566 n p) : term567 n p.
Proof. exact (@lem16684 (n = (NUMERAL 0)) (term87 n p) h1). Qed.
Lemma lem230950 (n : nat) (p : nat) (h1 : term565 n p) : (term566 n p) = (term567 n p).
Proof. exact (prop_ext (fun h2 : term566 n p => @lem230949 n p h2) (fun h2 : term567 n p => @lem230945 n p h1)). Qed.
Lemma lem230951 (n : nat) (p : nat) (h1 : term565 n p) : term567 n p.
Proof. exact (EQ_MP (@lem230950 n p h1) (@lem230945 n p h1)). Qed.
Lemma lem230952 (n : nat) (p : nat) (h1 : term566 n p) : term209 n.
Proof. exact (@lem16597 (n = (NUMERAL 0)) (term87 n p) h1). Qed.
Lemma lem230953 (n : nat) (p : nat) (h1 : term565 n p) : (term566 n p) = (term209 n).
Proof. exact (prop_ext (fun h2 : term566 n p => @lem230952 n p h2) (fun h2 : term209 n => @lem230945 n p h1)). Qed.
Lemma lem230954 (n : nat) (p : nat) (h1 : term565 n p) : term209 n.
Proof. exact (EQ_MP (@lem230953 n p h1) (@lem230945 n p h1)). Qed.
Lemma lem230955 (p : nat) (n : nat) (h1 : term356 p) (h2 : term209 n) : term568 p n.
Proof. exact (@lem16799 (term343 p) (n = (NUMERAL 0)) h1 h2). Qed.
Lemma lem230956 (n : nat) (p : nat) (h1 : term356 p) (h2 : term565 n p) : (term209 n) = (term568 p n).
Proof. exact (prop_ext (fun h3 : term209 n => @lem230955 p n h1 h3) (fun h3 : term568 p n => @lem230954 n p h2)). Qed.
Lemma lem230957 (n : nat) (p : nat) (h1 : term356 p) (h2 : term565 n p) : term568 p n.
Proof. exact (EQ_MP (@lem230956 n p h1 h2) (@lem230954 n p h2)). Qed.
Lemma lem230958 (n : nat) (p : nat) (h1 : term565 n p) : (term356 p) = (term568 p n).
Proof. exact (prop_ext (fun h2 : term356 p => @lem230957 n p h2 h1) (fun h2 : term568 p n => @lem230948 n p h1)). Qed.
Lemma lem230959 (n : nat) (p : nat) (h1 : term565 n p) : term568 p n.
Proof. exact (EQ_MP (@lem230958 n p h1) (@lem230948 n p h1)). Qed.
Lemma lem230960 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term568 p n) : term569 p n.
Proof. exact (@lem16799 (term87 n p) (term570 p n) h1 h2). Qed.
Lemma lem230961 (n : nat) (p : nat) (h1 : term567 n p) (h2 : term565 n p) : (term568 p n) = (term569 p n).
Proof. exact (prop_ext (fun h3 : term568 p n => @lem230960 p n h1 h3) (fun h3 : term569 p n => @lem230959 n p h2)). Qed.
Lemma lem230962 (n : nat) (p : nat) (h1 : term567 n p) (h2 : term565 n p) : term569 p n.
Proof. exact (EQ_MP (@lem230961 n p h1 h2) (@lem230959 n p h2)). Qed.
Lemma lem230963 (n : nat) (p : nat) (h1 : term565 n p) : (term567 n p) = (term569 p n).
Proof. exact (prop_ext (fun h2 : term567 n p => @lem230962 n p h2 h1) (fun h2 : term569 p n => @lem230951 n p h1)). Qed.
Lemma lem230964 (n : nat) (p : nat) (h1 : term565 n p) : term569 p n.
Proof. exact (EQ_MP (@lem230963 n p h1) (@lem230951 n p h1)). Qed.
Lemma lem230965 (p : nat) (n : nat) (h1 : term569 p n) : term569 p n.
Proof. exact (h1). Qed.
Lemma lem230966 (p : nat) (n : nat) (h1 : term569 p n) : term568 p n.
Proof. exact (@lem16684 (term87 n p) (term570 p n) h1). Qed.
Lemma lem230967 (p : nat) (n : nat) (h1 : term569 p n) : (term569 p n) = (term568 p n).
Proof. exact (prop_ext (fun h2 : term569 p n => @lem230966 p n h1) (fun h2 : term568 p n => @lem230965 p n h1)). Qed.
Lemma lem230968 (p : nat) (n : nat) (h1 : term569 p n) : term568 p n.
Proof. exact (EQ_MP (@lem230967 p n h1) (@lem230965 p n h1)). Qed.
Lemma lem230969 (p : nat) (n : nat) (h1 : term569 p n) : term567 n p.
Proof. exact (@lem16597 (term87 n p) (term570 p n) h1). Qed.
Lemma lem230970 (p : nat) (n : nat) (h1 : term569 p n) : (term569 p n) = (term567 n p).
Proof. exact (prop_ext (fun h2 : term569 p n => @lem230969 p n h1) (fun h2 : term567 n p => @lem230965 p n h1)). Qed.
Lemma lem230971 (p : nat) (n : nat) (h1 : term569 p n) : term567 n p.
Proof. exact (EQ_MP (@lem230970 p n h1) (@lem230965 p n h1)). Qed.
Lemma lem230972 (p : nat) (n : nat) (h1 : term568 p n) : term209 n.
Proof. exact (@lem16684 (term343 p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem230973 (p : nat) (n : nat) (h1 : term569 p n) : (term568 p n) = (term209 n).
Proof. exact (prop_ext (fun h2 : term568 p n => @lem230972 p n h2) (fun h2 : term209 n => @lem230968 p n h1)). Qed.
Lemma lem230974 (p : nat) (n : nat) (h1 : term569 p n) : term209 n.
Proof. exact (EQ_MP (@lem230973 p n h1) (@lem230968 p n h1)). Qed.
Lemma lem230975 (p : nat) (n : nat) (h1 : term568 p n) : term356 p.
Proof. exact (@lem16597 (term343 p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem230976 (p : nat) (n : nat) (h1 : term569 p n) : (term568 p n) = (term356 p).
Proof. exact (prop_ext (fun h2 : term568 p n => @lem230975 p n h2) (fun h2 : term356 p => @lem230968 p n h1)). Qed.
Lemma lem230977 (p : nat) (n : nat) (h1 : term569 p n) : term356 p.
Proof. exact (EQ_MP (@lem230976 p n h1) (@lem230968 p n h1)). Qed.
Lemma lem230978 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term209 n) : term566 n p.
Proof. exact (@lem16799 (n = (NUMERAL 0)) (term87 n p) h2 h1). Qed.
Lemma lem230979 (p : nat) (n : nat) (h1 : term209 n) (h2 : term569 p n) : (term567 n p) = (term566 n p).
Proof. exact (prop_ext (fun h3 : term567 n p => @lem230978 p n h3 h1) (fun h3 : term566 n p => @lem230971 p n h2)). Qed.
Lemma lem230980 (p : nat) (n : nat) (h1 : term209 n) (h2 : term569 p n) : term566 n p.
Proof. exact (EQ_MP (@lem230979 p n h1 h2) (@lem230971 p n h2)). Qed.
Lemma lem230981 (p : nat) (n : nat) (h1 : term569 p n) : (term209 n) = (term566 n p).
Proof. exact (prop_ext (fun h2 : term209 n => @lem230980 p n h2 h1) (fun h2 : term566 n p => @lem230974 p n h1)). Qed.
Lemma lem230982 (p : nat) (n : nat) (h1 : term569 p n) : term566 n p.
Proof. exact (EQ_MP (@lem230981 p n h1) (@lem230974 p n h1)). Qed.
Lemma lem230983 (n : nat) (p : nat) (h1 : term356 p) (h2 : term566 n p) : term565 n p.
Proof. exact (@lem16799 (term343 p) (term559 n p) h1 h2). Qed.
Lemma lem230984 (p : nat) (n : nat) (h1 : term356 p) (h2 : term569 p n) : (term566 n p) = (term565 n p).
Proof. exact (prop_ext (fun h3 : term566 n p => @lem230983 n p h1 h3) (fun h3 : term565 n p => @lem230982 p n h2)). Qed.
Lemma lem230985 (p : nat) (n : nat) (h1 : term356 p) (h2 : term569 p n) : term565 n p.
Proof. exact (EQ_MP (@lem230984 p n h1 h2) (@lem230982 p n h2)). Qed.
Lemma lem230986 (p : nat) (n : nat) (h1 : term569 p n) : (term356 p) = (term565 n p).
Proof. exact (prop_ext (fun h2 : term356 p => @lem230985 p n h2 h1) (fun h2 : term565 n p => @lem230977 p n h1)). Qed.
Lemma lem230987 (p : nat) (n : nat) (h1 : term569 p n) : term565 n p.
Proof. exact (EQ_MP (@lem230986 p n h1) (@lem230977 p n h1)). Qed.
Lemma lem230988 (n : nat) (p : nat) : term571 n p.
Proof. exact (fun h0 : term569 p n => @lem230987 p n h0). Qed.
Lemma lem230989 (p : nat) (n : nat) : term572 p n.
Proof. exact (fun h0 : term565 n p => @lem230964 n p h0). Qed.
Lemma lem230990 (n : nat) (p : nat) : term573 n p.
Proof. exact (conj (@lem230989 p n) (@lem230988 n p)). Qed.
Lemma lem230991 (p : nat) (n : nat) : (term573 n p) = ((term565 n p) = (term569 p n)).
Proof. exact (@lem32 (term565 n p) (term569 p n)). Qed.
Lemma lem230992 (p : nat) (n : nat) : (term565 n p) = (term569 p n).
Proof. exact (EQ_MP (@lem230991 p n) (@lem230990 n p)). Qed.
Lemma lem230993 (p : nat) (n : nat) (h1 : (term565 n p) = (term569 p n)) : (term564 n p) = (term574 p n).
Proof. exact (@lem16917 (term564 n p) (term574 p n) h1). Qed.
Lemma lem230994 (p : nat) (n : nat) : ((term565 n p) = (term569 p n)) = ((term564 n p) = (term574 p n)).
Proof. exact (prop_ext (fun h1 : (term565 n p) = (term569 p n) => @lem230993 p n h1) (fun h1 : (term564 n p) = (term574 p n) => @lem230992 p n)). Qed.
Lemma lem230995 (p : nat) (n : nat) : (term564 n p) = (term574 p n).
Proof. exact (EQ_MP (@lem230994 p n) (@lem230992 p n)). Qed.
Lemma lem230996 (p : nat) (n : nat) : term574 p n.
Proof. exact (EQ_MP (@lem230995 p n) (@lem230941 n p)). Qed.
Lemma lem231000 (p : nat) (h1 : p = (NUMERAL 0)) : (NUMERAL 0) = p.
Proof. exact (@lem230907 p h1 (@lem230900 p)). Qed.
Lemma lem231001 (p : nat) (n : nat) (h1 : term569 p n) : term569 p n.
Proof. exact (h1). Qed.
Lemma lem231002 (p : nat) (n : nat) (h1 : term569 p n) : term568 p n.
Proof. exact (@lem16684 (term87 n p) (term570 p n) h1). Qed.
Lemma lem231003 (p : nat) (n : nat) (h1 : term569 p n) : (term569 p n) = (term568 p n).
Proof. exact (prop_ext (fun h2 : term569 p n => @lem231002 p n h1) (fun h2 : term568 p n => @lem231001 p n h1)). Qed.
Lemma lem231004 (p : nat) (n : nat) (h1 : term569 p n) : term568 p n.
Proof. exact (EQ_MP (@lem231003 p n h1) (@lem231001 p n h1)). Qed.
Lemma lem231005 (p : nat) (n : nat) (h1 : term569 p n) : term567 n p.
Proof. exact (@lem16597 (term87 n p) (term570 p n) h1). Qed.
Lemma lem231006 (p : nat) (n : nat) (h1 : term569 p n) : (term569 p n) = (term567 n p).
Proof. exact (prop_ext (fun h2 : term569 p n => @lem231005 p n h1) (fun h2 : term567 n p => @lem231001 p n h1)). Qed.
Lemma lem231007 (p : nat) (n : nat) (h1 : term569 p n) : term567 n p.
Proof. exact (EQ_MP (@lem231006 p n h1) (@lem231001 p n h1)). Qed.
Lemma lem231008 (p : nat) (n : nat) (h1 : term568 p n) : term209 n.
Proof. exact (@lem16684 (term343 p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem231009 (p : nat) (n : nat) (h1 : term569 p n) : (term568 p n) = (term209 n).
Proof. exact (prop_ext (fun h2 : term568 p n => @lem231008 p n h2) (fun h2 : term209 n => @lem231004 p n h1)). Qed.
Lemma lem231010 (p : nat) (n : nat) (h1 : term569 p n) : term209 n.
Proof. exact (EQ_MP (@lem231009 p n h1) (@lem231004 p n h1)). Qed.
Lemma lem231011 (p : nat) (n : nat) (h1 : term568 p n) : term356 p.
Proof. exact (@lem16597 (term343 p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem231012 (p : nat) (n : nat) (h1 : term569 p n) : (term568 p n) = (term356 p).
Proof. exact (prop_ext (fun h2 : term568 p n => @lem231011 p n h2) (fun h2 : term356 p => @lem231004 p n h1)). Qed.
Lemma lem231013 (p : nat) (n : nat) (h1 : term569 p n) : term356 p.
Proof. exact (EQ_MP (@lem231012 p n h1) (@lem231004 p n h1)). Qed.
Lemma lem231014 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term209 n) : term575 p n.
Proof. exact (@lem16799 (term87 n p) (n = (NUMERAL 0)) h1 h2). Qed.
Lemma lem231015 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term569 p n) : (term209 n) = (term575 p n).
Proof. exact (prop_ext (fun h3 : term209 n => @lem231014 p n h1 h3) (fun h3 : term575 p n => @lem231010 p n h2)). Qed.
Lemma lem231016 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term569 p n) : term575 p n.
Proof. exact (EQ_MP (@lem231015 p n h1 h2) (@lem231010 p n h2)). Qed.
Lemma lem231017 (p : nat) (n : nat) (h1 : term569 p n) : (term567 n p) = (term575 p n).
Proof. exact (prop_ext (fun h2 : term567 n p => @lem231016 p n h2 h1) (fun h2 : term575 p n => @lem231007 p n h1)). Qed.
Lemma lem231018 (p : nat) (n : nat) (h1 : term569 p n) : term575 p n.
Proof. exact (EQ_MP (@lem231017 p n h1) (@lem231007 p n h1)). Qed.
Lemma lem231019 (p : nat) (n : nat) (h1 : term356 p) (h2 : term575 p n) : term576 p n.
Proof. exact (@lem16799 (term343 p) (term577 p n) h1 h2). Qed.
Lemma lem231020 (p : nat) (n : nat) (h1 : term356 p) (h2 : term569 p n) : (term575 p n) = (term576 p n).
Proof. exact (prop_ext (fun h3 : term575 p n => @lem231019 p n h1 h3) (fun h3 : term576 p n => @lem231018 p n h2)). Qed.
Lemma lem231021 (p : nat) (n : nat) (h1 : term356 p) (h2 : term569 p n) : term576 p n.
Proof. exact (EQ_MP (@lem231020 p n h1 h2) (@lem231018 p n h2)). Qed.
Lemma lem231022 (p : nat) (n : nat) (h1 : term569 p n) : (term356 p) = (term576 p n).
Proof. exact (prop_ext (fun h2 : term356 p => @lem231021 p n h2 h1) (fun h2 : term576 p n => @lem231013 p n h1)). Qed.
Lemma lem231023 (p : nat) (n : nat) (h1 : term569 p n) : term576 p n.
Proof. exact (EQ_MP (@lem231022 p n h1) (@lem231013 p n h1)). Qed.
Lemma lem231024 (p : nat) (n : nat) (h1 : term576 p n) : term576 p n.
Proof. exact (h1). Qed.
Lemma lem231025 (p : nat) (n : nat) (h1 : term576 p n) : term575 p n.
Proof. exact (@lem16684 (term343 p) (term577 p n) h1). Qed.
Lemma lem231026 (p : nat) (n : nat) (h1 : term576 p n) : (term576 p n) = (term575 p n).
Proof. exact (prop_ext (fun h2 : term576 p n => @lem231025 p n h1) (fun h2 : term575 p n => @lem231024 p n h1)). Qed.
Lemma lem231027 (p : nat) (n : nat) (h1 : term576 p n) : term575 p n.
Proof. exact (EQ_MP (@lem231026 p n h1) (@lem231024 p n h1)). Qed.
Lemma lem231028 (p : nat) (n : nat) (h1 : term576 p n) : term356 p.
Proof. exact (@lem16597 (term343 p) (term577 p n) h1). Qed.
Lemma lem231029 (p : nat) (n : nat) (h1 : term576 p n) : (term576 p n) = (term356 p).
Proof. exact (prop_ext (fun h2 : term576 p n => @lem231028 p n h1) (fun h2 : term356 p => @lem231024 p n h1)). Qed.
Lemma lem231030 (p : nat) (n : nat) (h1 : term576 p n) : term356 p.
Proof. exact (EQ_MP (@lem231029 p n h1) (@lem231024 p n h1)). Qed.
Lemma lem231031 (p : nat) (n : nat) (h1 : term575 p n) : term209 n.
Proof. exact (@lem16684 (term87 n p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem231032 (p : nat) (n : nat) (h1 : term576 p n) : (term575 p n) = (term209 n).
Proof. exact (prop_ext (fun h2 : term575 p n => @lem231031 p n h2) (fun h2 : term209 n => @lem231027 p n h1)). Qed.
Lemma lem231033 (p : nat) (n : nat) (h1 : term576 p n) : term209 n.
Proof. exact (EQ_MP (@lem231032 p n h1) (@lem231027 p n h1)). Qed.
Lemma lem231034 (p : nat) (n : nat) (h1 : term575 p n) : term567 n p.
Proof. exact (@lem16597 (term87 n p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem231035 (p : nat) (n : nat) (h1 : term576 p n) : (term575 p n) = (term567 n p).
Proof. exact (prop_ext (fun h2 : term575 p n => @lem231034 p n h2) (fun h2 : term567 n p => @lem231027 p n h1)). Qed.
Lemma lem231036 (p : nat) (n : nat) (h1 : term576 p n) : term567 n p.
Proof. exact (EQ_MP (@lem231035 p n h1) (@lem231027 p n h1)). Qed.
Lemma lem231037 (p : nat) (n : nat) (h1 : term356 p) (h2 : term209 n) : term568 p n.
Proof. exact (@lem16799 (term343 p) (n = (NUMERAL 0)) h1 h2). Qed.
Lemma lem231038 (p : nat) (n : nat) (h1 : term356 p) (h2 : term576 p n) : (term209 n) = (term568 p n).
Proof. exact (prop_ext (fun h3 : term209 n => @lem231037 p n h1 h3) (fun h3 : term568 p n => @lem231033 p n h2)). Qed.
Lemma lem231039 (p : nat) (n : nat) (h1 : term356 p) (h2 : term576 p n) : term568 p n.
Proof. exact (EQ_MP (@lem231038 p n h1 h2) (@lem231033 p n h2)). Qed.
Lemma lem231040 (p : nat) (n : nat) (h1 : term576 p n) : (term356 p) = (term568 p n).
Proof. exact (prop_ext (fun h2 : term356 p => @lem231039 p n h2 h1) (fun h2 : term568 p n => @lem231030 p n h1)). Qed.
Lemma lem231041 (p : nat) (n : nat) (h1 : term576 p n) : term568 p n.
Proof. exact (EQ_MP (@lem231040 p n h1) (@lem231030 p n h1)). Qed.
Lemma lem231042 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term568 p n) : term569 p n.
Proof. exact (@lem16799 (term87 n p) (term570 p n) h1 h2). Qed.
Lemma lem231043 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term576 p n) : (term568 p n) = (term569 p n).
Proof. exact (prop_ext (fun h3 : term568 p n => @lem231042 p n h1 h3) (fun h3 : term569 p n => @lem231041 p n h2)). Qed.
Lemma lem231044 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term576 p n) : term569 p n.
Proof. exact (EQ_MP (@lem231043 p n h1 h2) (@lem231041 p n h2)). Qed.
Lemma lem231045 (p : nat) (n : nat) (h1 : term576 p n) : (term567 n p) = (term569 p n).
Proof. exact (prop_ext (fun h2 : term567 n p => @lem231044 p n h2 h1) (fun h2 : term569 p n => @lem231036 p n h1)). Qed.
Lemma lem231046 (p : nat) (n : nat) (h1 : term576 p n) : term569 p n.
Proof. exact (EQ_MP (@lem231045 p n h1) (@lem231036 p n h1)). Qed.
Lemma lem231047 (p : nat) (n : nat) : term578 p n.
Proof. exact (fun h0 : term576 p n => @lem231046 p n h0). Qed.
Lemma lem231048 (p : nat) (n : nat) : term579 p n.
Proof. exact (fun h0 : term569 p n => @lem231023 p n h0). Qed.
Lemma lem231049 (p : nat) (n : nat) : term580 p n.
Proof. exact (conj (@lem231048 p n) (@lem231047 p n)). Qed.
Lemma lem231050 (p : nat) (n : nat) : (term580 p n) = ((term569 p n) = (term576 p n)).
Proof. exact (@lem32 (term569 p n) (term576 p n)). Qed.
Lemma lem231051 (p : nat) (n : nat) : (term569 p n) = (term576 p n).
Proof. exact (EQ_MP (@lem231050 p n) (@lem231049 p n)). Qed.
Lemma lem231052 (p : nat) (n : nat) (h1 : (term569 p n) = (term576 p n)) : (term574 p n) = (term581 p n).
Proof. exact (@lem16917 (term574 p n) (term581 p n) h1). Qed.
Lemma lem231053 (p : nat) (n : nat) : ((term569 p n) = (term576 p n)) = ((term574 p n) = (term581 p n)).
Proof. exact (prop_ext (fun h1 : (term569 p n) = (term576 p n) => @lem231052 p n h1) (fun h1 : (term574 p n) = (term581 p n) => @lem231051 p n)). Qed.
Lemma lem231056 (p : nat) (n : nat) : (term574 p n) = (term581 p n).
Proof. exact (EQ_MP (@lem231053 p n) (@lem231051 p n)). Qed.
Lemma lem231057 (p : nat) (n : nat) : term581 p n.
Proof. exact (EQ_MP (@lem231056 p n) (@lem230996 p n)). Qed.
Lemma lem231058 (p : nat) : term371 p.
Proof. exact (@lem22025 ((NUMERAL 0) = p)). Qed.
Lemma lem231059 (p : nat) : (term371 p) = (term372 p).
Proof. exact (eq_refl (term371 p)). Qed.
Lemma lem231060 (p : nat) : term372 p.
Proof. exact (EQ_MP (@lem231059 p) (@lem231058 p)). Qed.
Lemma lem231061 (p : nat) (n : nat) : term582 p n.
Proof. exact (@lem231060 p (term577 p n)). Qed.
Lemma lem231062 (p : nat) (n : nat) : (term582 p n) = (term583 p n).
Proof. exact (eq_refl (term582 p n)). Qed.
Lemma lem231063 (p : nat) (n : nat) : term583 p n.
Proof. exact (EQ_MP (@lem231062 p n) (@lem231061 p n)). Qed.
Lemma lem231064 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term584 p n.
Proof. exact (@lem231063 p n (@lem231000 p h1)). Qed.
Lemma lem231067 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term577 p n.
Proof. exact (@lem231064 n p h1 (@lem231057 p n)). Qed.
Lemma lem231070 (p : nat) (n : nat) (h1 : term575 p n) : term575 p n.
Proof. exact (h1). Qed.
Lemma lem231071 (p : nat) (n : nat) (h1 : term575 p n) : term209 n.
Proof. exact (@lem16684 (term87 n p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem231072 (p : nat) (n : nat) (h1 : term575 p n) : (term575 p n) = (term209 n).
Proof. exact (prop_ext (fun h2 : term575 p n => @lem231071 p n h1) (fun h2 : term209 n => @lem231070 p n h1)). Qed.
Lemma lem231073 (p : nat) (n : nat) (h1 : term575 p n) : term209 n.
Proof. exact (EQ_MP (@lem231072 p n h1) (@lem231070 p n h1)). Qed.
Lemma lem231074 (p : nat) (n : nat) (h1 : term575 p n) : term567 n p.
Proof. exact (@lem16597 (term87 n p) (n = (NUMERAL 0)) h1). Qed.
Lemma lem231075 (p : nat) (n : nat) (h1 : term575 p n) : (term575 p n) = (term567 n p).
Proof. exact (prop_ext (fun h2 : term575 p n => @lem231074 p n h1) (fun h2 : term567 n p => @lem231070 p n h1)). Qed.
Lemma lem231076 (p : nat) (n : nat) (h1 : term575 p n) : term567 n p.
Proof. exact (EQ_MP (@lem231075 p n h1) (@lem231070 p n h1)). Qed.
Lemma lem231077 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term209 n) : term566 n p.
Proof. exact (@lem16799 (n = (NUMERAL 0)) (term87 n p) h2 h1). Qed.
Lemma lem231078 (p : nat) (n : nat) (h1 : term209 n) (h2 : term575 p n) : (term567 n p) = (term566 n p).
Proof. exact (prop_ext (fun h3 : term567 n p => @lem231077 p n h3 h1) (fun h3 : term566 n p => @lem231076 p n h2)). Qed.
Lemma lem231079 (p : nat) (n : nat) (h1 : term209 n) (h2 : term575 p n) : term566 n p.
Proof. exact (EQ_MP (@lem231078 p n h1 h2) (@lem231076 p n h2)). Qed.
Lemma lem231080 (p : nat) (n : nat) (h1 : term575 p n) : (term209 n) = (term566 n p).
Proof. exact (prop_ext (fun h2 : term209 n => @lem231079 p n h2 h1) (fun h2 : term566 n p => @lem231073 p n h1)). Qed.
Lemma lem231081 (p : nat) (n : nat) (h1 : term575 p n) : term566 n p.
Proof. exact (EQ_MP (@lem231080 p n h1) (@lem231073 p n h1)). Qed.
Lemma lem231082 (n : nat) (p : nat) (h1 : term566 n p) : term566 n p.
Proof. exact (h1). Qed.
Lemma lem231083 (n : nat) (p : nat) (h1 : term566 n p) : term567 n p.
Proof. exact (@lem16684 (n = (NUMERAL 0)) (term87 n p) h1). Qed.
Lemma lem231084 (n : nat) (p : nat) (h1 : term566 n p) : (term566 n p) = (term567 n p).
Proof. exact (prop_ext (fun h2 : term566 n p => @lem231083 n p h1) (fun h2 : term567 n p => @lem231082 n p h1)). Qed.
Lemma lem231085 (n : nat) (p : nat) (h1 : term566 n p) : term567 n p.
Proof. exact (EQ_MP (@lem231084 n p h1) (@lem231082 n p h1)). Qed.
Lemma lem231086 (n : nat) (p : nat) (h1 : term566 n p) : term209 n.
Proof. exact (@lem16597 (n = (NUMERAL 0)) (term87 n p) h1). Qed.
Lemma lem231087 (n : nat) (p : nat) (h1 : term566 n p) : (term566 n p) = (term209 n).
Proof. exact (prop_ext (fun h2 : term566 n p => @lem231086 n p h1) (fun h2 : term209 n => @lem231082 n p h1)). Qed.
Lemma lem231088 (n : nat) (p : nat) (h1 : term566 n p) : term209 n.
Proof. exact (EQ_MP (@lem231087 n p h1) (@lem231082 n p h1)). Qed.
Lemma lem231089 (p : nat) (n : nat) (h1 : term567 n p) (h2 : term209 n) : term575 p n.
Proof. exact (@lem16799 (term87 n p) (n = (NUMERAL 0)) h1 h2). Qed.
Lemma lem231090 (n : nat) (p : nat) (h1 : term567 n p) (h2 : term566 n p) : (term209 n) = (term575 p n).
Proof. exact (prop_ext (fun h3 : term209 n => @lem231089 p n h1 h3) (fun h3 : term575 p n => @lem231088 n p h2)). Qed.
Lemma lem231091 (n : nat) (p : nat) (h1 : term567 n p) (h2 : term566 n p) : term575 p n.
Proof. exact (EQ_MP (@lem231090 n p h1 h2) (@lem231088 n p h2)). Qed.
Lemma lem231092 (n : nat) (p : nat) (h1 : term566 n p) : (term567 n p) = (term575 p n).
Proof. exact (prop_ext (fun h2 : term567 n p => @lem231091 n p h2 h1) (fun h2 : term575 p n => @lem231085 n p h1)). Qed.
Lemma lem231093 (n : nat) (p : nat) (h1 : term566 n p) : term575 p n.
Proof. exact (EQ_MP (@lem231092 n p h1) (@lem231085 n p h1)). Qed.
Lemma lem231094 (p : nat) (n : nat) : term585 p n.
Proof. exact (fun h0 : term566 n p => @lem231093 n p h0). Qed.
Lemma lem231095 (n : nat) (p : nat) : term586 n p.
Proof. exact (fun h0 : term575 p n => @lem231081 p n h0). Qed.
Lemma lem231096 (p : nat) (n : nat) : term587 p n.
Proof. exact (conj (@lem231095 n p) (@lem231094 p n)). Qed.
Lemma lem231097 (n : nat) (p : nat) : (term587 p n) = ((term575 p n) = (term566 n p)).
Proof. exact (@lem32 (term575 p n) (term566 n p)). Qed.
Lemma lem231098 (n : nat) (p : nat) : (term575 p n) = (term566 n p).
Proof. exact (EQ_MP (@lem231097 n p) (@lem231096 p n)). Qed.
Lemma lem231099 (n : nat) (p : nat) (h1 : (term575 p n) = (term566 n p)) : (term577 p n) = (term559 n p).
Proof. exact (@lem16917 (term577 p n) (term559 n p) h1). Qed.
Lemma lem231100 (n : nat) (p : nat) : ((term575 p n) = (term566 n p)) = ((term577 p n) = (term559 n p)).
Proof. exact (prop_ext (fun h1 : (term575 p n) = (term566 n p) => @lem231099 n p h1) (fun h1 : (term577 p n) = (term559 n p) => @lem231098 n p)). Qed.
Lemma lem231103 (n : nat) (p : nat) : (term577 p n) = (term559 n p).
Proof. exact (EQ_MP (@lem231100 n p) (@lem231098 n p)). Qed.
Lemma lem231104 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term559 n p.
Proof. exact (EQ_MP (@lem231103 n p) (@lem231067 n p h1)). Qed.
Lemma lem231108 (n : nat) (h1 : term209 n) : term209 n.
Proof. exact (h1). Qed.
Lemma lem231109 (n : nat) : term588 n.
Proof. exact (@lem21930 (n = (NUMERAL 0))). Qed.
Lemma lem231110 (n : nat) : (term588 n) = (term589 n).
Proof. exact (eq_refl (term588 n)). Qed.
Lemma lem231111 (n : nat) : term589 n.
Proof. exact (EQ_MP (@lem231110 n) (@lem231109 n)). Qed.
Lemma lem231112 (n : nat) (p : nat) : term590 n p.
Proof. exact (@lem231111 n (term87 n p)). Qed.
Lemma lem231113 (n : nat) (p : nat) : (term590 n p) = (term591 n p).
Proof. exact (eq_refl (term590 n p)). Qed.
Lemma lem231114 (n : nat) (p : nat) : term591 n p.
Proof. exact (EQ_MP (@lem231113 n p) (@lem231112 n p)). Qed.
Lemma lem231115 (n : nat) (p : nat) (h1 : p = (NUMERAL 0)) : term555 n p.
Proof. exact (@lem231114 n p (@lem231104 n p h1)). Qed.
Lemma lem231124 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : p = (NUMERAL 0)) : n = p.
Proof. exact (@lem230772 m n p (@lem230765 m n p h1 h2 h3 h4)). Qed.
Lemma lem231128 (n : nat) (p : nat) (h1 : term209 n) (h2 : p = (NUMERAL 0)) : term87 n p.
Proof. exact (@lem231115 n p h2 (@lem231108 n h1)). Qed.
Lemma lem231129 (n : nat) (p : nat) : term592 n p.
Proof. exact (@lem21816 (n = p)). Qed.
Lemma lem231130 (n : nat) (p : nat) : (term592 n p) = (term593 n p).
Proof. exact (eq_refl (term592 n p)). Qed.
Lemma lem231131 (n : nat) (p : nat) : term593 n p.
Proof. exact (EQ_MP (@lem231130 n p) (@lem231129 n p)). Qed.
Lemma lem231132 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : p = (NUMERAL 0)) : term594 n p.
Proof. exact (@lem231131 n p (@lem231124 m n p h1 h2 h3 h4)). Qed.
Lemma lem231135 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (@lem231132 m n p h1 h2 h3 h5 (@lem231128 n p h4 h5)). Qed.
Lemma lem231136 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term239 m n) = False.
Proof. exact (prop_ext (fun h6 : term239 m n => @lem231135 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229326 m n h3)). Qed.
Lemma lem231137 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231136 m n p h1 h2 h3 h4 h5) (@lem229326 m n h3)). Qed.
Lemma lem231138 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (p = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : p = (NUMERAL 0) => @lem231137 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229324 p h5)). Qed.
Lemma lem231139 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231138 m n p h1 h2 h3 h4 h5) (@lem229324 p h5)). Qed.
Lemma lem231140 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term209 n) = False.
Proof. exact (prop_ext (fun h6 : term209 n => @lem231139 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229322 n h4)). Qed.
Lemma lem231141 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231140 m n p h1 h2 h3 h4 h5) (@lem229322 n h4)). Qed.
Lemma lem231142 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term239 m n) = False.
Proof. exact (prop_ext (fun h6 : term239 m n => @lem231141 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229270 m n h3)). Qed.
Lemma lem231143 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231142 m n p h1 h2 h3 h4 h5) (@lem229270 m n h3)). Qed.
Lemma lem231144 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (p = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : p = (NUMERAL 0) => @lem231143 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229266 p h5)). Qed.
Lemma lem231145 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231144 m n p h1 h2 h3 h4 h5) (@lem229266 p h5)). Qed.
Lemma lem231146 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term209 n) = False.
Proof. exact (prop_ext (fun h6 : term209 n => @lem231145 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229262 n h4)). Qed.
Lemma lem231147 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231146 m n p h1 h2 h3 h4 h5) (@lem229262 n h4)). Qed.
Lemma lem231148 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : term277 = False.
Proof. exact (prop_ext (fun h6 : term277 => @lem231147 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229280 h1)). Qed.
Lemma lem231149 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231148 m n p h1 h2 h3 h4 h5) (@lem229280 h1)). Qed.
Lemma lem231150 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term239 m n) = False.
Proof. exact (prop_ext (fun h6 : term239 m n => @lem231149 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229270 m n h3)). Qed.
Lemma lem231151 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231150 m n p h1 h2 h3 h4 h5) (@lem229270 m n h3)). Qed.
Lemma lem231152 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (p = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : p = (NUMERAL 0) => @lem231151 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229266 p h5)). Qed.
Lemma lem231153 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231152 m n p h1 h2 h3 h4 h5) (@lem229266 p h5)). Qed.
Lemma lem231154 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term209 n) = False.
Proof. exact (prop_ext (fun h6 : term209 n => @lem231153 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229262 n h4)). Qed.
Lemma lem231155 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231154 m n p h1 h2 h3 h4 h5) (@lem229262 n h4)). Qed.
Lemma lem231156 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : term277 = False.
Proof. exact (prop_ext (fun h6 : term277 => @lem231155 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229208 h1)). Qed.
Lemma lem231157 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231156 m n p h1 h2 h3 h4 h5) (@lem229208 h1)). Qed.
Lemma lem231158 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term239 m n) = False.
Proof. exact (prop_ext (fun h6 : term239 m n => @lem231157 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229188 m n h3)). Qed.
Lemma lem231159 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231158 m n p h1 h2 h3 h4 h5) (@lem229188 m n h3)). Qed.
Lemma lem231160 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (p = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : p = (NUMERAL 0) => @lem231159 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229164 p h5)). Qed.
Lemma lem231161 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231160 m n p h1 h2 h3 h4 h5) (@lem229164 p h5)). Qed.
Lemma lem231162 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term209 n) = False.
Proof. exact (prop_ext (fun h6 : term209 n => @lem231161 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229156 n h4)). Qed.
Lemma lem231163 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231162 m n p h1 h2 h3 h4 h5) (@lem229156 n h4)). Qed.
Lemma lem231164 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : term277 = False.
Proof. exact (prop_ext (fun h6 : term277 => @lem231163 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229070 h1)). Qed.
Lemma lem231165 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231164 m n p h1 h2 h3 h4 h5) (@lem229070 h1)). Qed.
Lemma lem231166 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term239 m n) = False.
Proof. exact (prop_ext (fun h6 : term239 m n => @lem231165 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229050 m n h3)). Qed.
Lemma lem231167 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231166 m n p h1 h2 h3 h4 h5) (@lem229050 m n h3)). Qed.
Lemma lem231168 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (p = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : p = (NUMERAL 0) => @lem231167 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229044 p h5)). Qed.
Lemma lem231169 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231168 m n p h1 h2 h3 h4 h5) (@lem229044 p h5)). Qed.
Lemma lem231170 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : (term209 n) = False.
Proof. exact (prop_ext (fun h6 : term209 n => @lem231169 m n p h1 h2 h3 h4 h5) (fun h6 : False => @lem229038 n h4)). Qed.
Lemma lem231171 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term246) (h3 : term239 m n) (h4 : term209 n) (h5 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231170 m n p h1 h2 h3 h4 h5) (@lem229038 n h4)). Qed.
Lemma lem231172 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term239 m n) (h3 : term209 n) (h4 : p = (NUMERAL 0)) : term244.
Proof. exact (fun h0 : term246 => @lem231171 m n p h1 h0 h2 h3 h4). Qed.
Lemma lem231173 : term244 = term245.
Proof. exact (@lem69 term246). Qed.
Lemma lem231174 (m : nat) (n : nat) (p : nat) (h1 : term277) (h2 : term239 m n) (h3 : term209 n) (h4 : p = (NUMERAL 0)) : term245.
Proof. exact (EQ_MP (@lem231173) (@lem231172 m n p h1 h2 h3 h4)). Qed.
Lemma lem231175 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term209 n) (h3 : p = (NUMERAL 0)) : term249.
Proof. exact (fun h0 : term277 => @lem231174 m n p h0 h1 h2 h3). Qed.
Lemma lem231176 (m : nat) (n : nat) (p : nat) (h1 : term209 n) (h2 : p = (NUMERAL 0)) : term252 m n.
Proof. exact (fun h0 : term239 m n => @lem231175 m n p h0 h1 h2). Qed.
Lemma lem231177 (p : nat) (m : nat) (n : nat) (h1 : term209 n) : term255 p m n.
Proof. exact (fun h0 : p = (NUMERAL 0) => @lem231176 m n p h1 h0). Qed.
Lemma lem231178 (p : nat) (m : nat) (n : nat) : term257 p m n.
Proof. exact (fun h0 : term209 n => @lem231177 p m n h0). Qed.
Lemma lem231183 (m : nat) (n : nat) : term261 m n.
Proof. exact (fun p : nat => @lem231178 p m n). Qed.
Lemma lem231188 (n : nat) : term265 n.
Proof. exact (fun m : nat => @lem231183 m n). Qed.
Lemma lem231193 : term269.
Proof. exact (fun n : nat => @lem231188 n). Qed.
Lemma lem231194 : term268.
Proof. exact (EQ_MP (@lem229027) (@lem231193)). Qed.
Lemma lem231195 (n : nat) : term595 n.
Proof. exact (@lem231194 n). Qed.
Lemma lem231196 (n : nat) : (term595 n) = (term264 n).
Proof. exact (eq_refl (term595 n)). Qed.
Lemma lem231197 (n : nat) : term264 n.
Proof. exact (EQ_MP (@lem231196 n) (@lem231195 n)). Qed.
Lemma lem231198 (n : nat) (m : nat) : term596 n m.
Proof. exact (@lem231197 n m). Qed.
Lemma lem231199 (m : nat) (n : nat) : (term596 n m) = (term260 m n).
Proof. exact (eq_refl (term596 n m)). Qed.
Lemma lem231200 (m : nat) (n : nat) : term260 m n.
Proof. exact (EQ_MP (@lem231199 m n) (@lem231198 n m)). Qed.
Lemma lem231201 (m : nat) (n : nat) (p : nat) : term597 m n p.
Proof. exact (@lem231200 m n p). Qed.
Lemma lem231202 (p : nat) (m : nat) (n : nat) : (term597 m n p) = (term240 p m n).
Proof. exact (eq_refl (term597 m n p)). Qed.
Lemma lem231203 (p : nat) (m : nat) (n : nat) : term240 p m n.
Proof. exact (EQ_MP (@lem231202 p m n) (@lem231201 m n p)). Qed.
Lemma lem231205 (p : nat) (m : nat) (n : nat) : term240 p m n.
Proof. exact (@lem228831 p m n (@lem231203 p m n)). Qed.
Lemma lem231206 (p : nat) (m : nat) (n : nat) (h1 : term209 n) : term254 p m n.
Proof. exact (@lem231205 p m n (@lem228526 n h1)). Qed.
Lemma lem231207 (m : nat) (n : nat) (p : nat) (h1 : term209 n) (h2 : p = (NUMERAL 0)) : term251 m n.
Proof. exact (@lem231206 p m n h1 (@lem228520 p h2)). Qed.
Lemma lem231208 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term209 n) (h3 : p = (NUMERAL 0)) : term248.
Proof. exact (@lem231207 m n p h2 h3 (@lem228816 m n h1)). Qed.
Lemma lem231209 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term209 n) (h3 : p = (NUMERAL 0)) : term244.
Proof. exact (@lem231208 m n p h1 h2 h3 (@lem81820)). Qed.
Lemma lem231210 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term209 n) (h3 : p = (NUMERAL 0)) : False.
Proof. exact (@lem231209 m n p h1 h2 h3 (@lem157261)). Qed.
Lemma lem231211 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term209 n) (h3 : p = (NUMERAL 0)) : (term239 m n) = False.
Proof. exact (prop_ext (fun h4 : term239 m n => @lem231210 m n p h1 h2 h3) (fun h4 : False => @lem228816 m n h1)). Qed.
Lemma lem231212 (m : nat) (n : nat) (p : nat) (h1 : term239 m n) (h2 : term209 n) (h3 : p = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem231211 m n p h1 h2 h3) (@lem228816 m n h1)). Qed.
Lemma lem231213 (m : nat) (n : nat) (p : nat) (h1 : term209 n) (h2 : p = (NUMERAL 0)) : term238 m n.
Proof. exact (fun h0 : term239 m n => @lem231212 m n p h0 h1 h2). Qed.
Lemma lem231214 (m : nat) (n : nat) (p : nat) (h1 : term209 n) (h2 : p = (NUMERAL 0)) : m = (term4 m n).
Proof. exact (EQ_MP (@lem228815 m n) (@lem231213 m n p h1 h2)). Qed.
Lemma lem231215 (m : nat) (n : nat) (p : nat) (h1 : term209 n) (h2 : p = (NUMERAL 0)) : (term219 m n p) = (term230 p m n).
Proof. exact (EQ_MP (@lem228811 m n p h2) (@lem231214 m n p h1 h2)). Qed.
Lemma lem231217 (x : nat) (y : nat) : term59 x y.
Proof. exact (@lem228505 x y (@lem228497 x y)). Qed.
Lemma lem231218 (p : nat) (m : nat) (n : nat) : term598 p m n.
Proof. exact (@lem231217 (term219 m n p) (term230 p m n)). Qed.
Lemma lem231224 (m : nat) (n : nat) (p : nat) : (term10 m n p) = (term11 m n p).
Proof. exact (EQ_MP (@lem227530 m n p) (@lem227529 m n p)). Qed.
Lemma lem231225 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem231226 (m : nat) (n : nat) (p : nat) : (term599 m n p) = (term600 m n p).
Proof. exact (MK_COMB (@lem231225) (@lem231224 m n p)). Qed.
Lemma lem231227 (n : nat) (p : nat) : (Nat.mul n p) = (Nat.mul n p).
Proof. exact (eq_refl (Nat.mul n p)). Qed.
Lemma lem231228 (m : nat) (n : nat) (p : nat) : (term601 m n p) = (term602 m n p).
Proof. exact (MK_COMB (@lem231226 m n p) (@lem231227 n p)). Qed.
Lemma lem231229 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem231230 (m : nat) (n : nat) (p : nat) : (term603 m n p) = (term604 m n p).
Proof. exact (MK_COMB (@lem231229) (@lem231228 m n p)). Qed.
Lemma lem231231 (m : nat) (n : nat) (p : nat) : (term219 m n p) = (term219 m n p).
Proof. exact (eq_refl (term219 m n p)). Qed.
Lemma lem231232 (m : nat) (n : nat) (p : nat) : (term605 m n p) = (term606 m n p).
Proof. exact (MK_COMB (@lem231230 m n p) (@lem231231 m n p)). Qed.
Lemma lem231234 (n : nat) (m : nat) : (term9 m n) = m.
Proof. exact (EQ_MP (@lem227544 n m) (@lem227543 m n)). Qed.
Lemma lem231235 (n : nat) (p : nat) (m : nat) : (term606 m n p) = m.
Proof. exact (@lem231234 (Nat.mul n p) m). Qed.
Lemma lem231236 (n : nat) (p : nat) (m : nat) : (term605 m n p) = m.
Proof. exact (TRANS (@lem231232 m n p) (@lem231235 n p m)). Qed.
Lemma lem231237 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem231238 (n : nat) (p : nat) (m : nat) : (term607 m n p) = (@eq nat m).
Proof. exact (MK_COMB (@lem231237) (@lem231236 n p m)). Qed.
Lemma lem231240 (m : nat) (n : nat) (p : nat) : (term10 m n p) = (term11 m n p).
Proof. exact (EQ_MP (@lem227530 m n p) (@lem227529 m n p)). Qed.
Lemma lem231241 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem231242 (m : nat) (n : nat) (p : nat) : (term599 m n p) = (term600 m n p).
Proof. exact (MK_COMB (@lem231241) (@lem231240 m n p)). Qed.
Lemma lem231243 (n : nat) (p : nat) : (Nat.mul n p) = (Nat.mul n p).
Proof. exact (eq_refl (Nat.mul n p)). Qed.
Lemma lem231244 (m : nat) (n : nat) (p : nat) : (term601 m n p) = (term602 m n p).
Proof. exact (MK_COMB (@lem231242 m n p) (@lem231243 n p)). Qed.
Lemma lem231245 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem231246 (m : nat) (n : nat) (p : nat) : (term603 m n p) = (term604 m n p).
Proof. exact (MK_COMB (@lem231245) (@lem231244 m n p)). Qed.
Lemma lem231247 (p : nat) (m : nat) (n : nat) : (term230 p m n) = (term230 p m n).
Proof. exact (eq_refl (term230 p m n)). Qed.
Lemma lem231248 (p : nat) (m : nat) (n : nat) : (term608 p m n) = (term609 p m n).
Proof. exact (MK_COMB (@lem231246 m n p) (@lem231247 p m n)). Qed.
Lemma lem231249 (p : nat) (m : nat) (n : nat) : ((term605 m n p) = (term608 p m n)) = (m = (term609 p m n)).
Proof. exact (MK_COMB (@lem231238 n p m) (@lem231248 p m n)). Qed.
Lemma lem231252 (p : nat) (m : nat) (n : nat) : (m = (term609 p m n)) = ((term605 m n p) = (term608 p m n)).
Proof. exact (SYM (@lem231249 p m n)). Qed.
Lemma lem231256 (n : nat) (d : nat) (p : nat) : (term53 d n p) = (term53 n d p).
Proof. exact (EQ_MP (@lem227521 n d p) (@lem0)). Qed.
Lemma lem231257 (m : nat) (n : nat) (p : nat) : (term602 m n p) = (term610 m n p).
Proof. exact (@lem231256 n (term11 m n p) p). Qed.
Lemma lem231261 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem231262 (m : nat) (n : nat) (p : nat) : (term604 m n p) = (term611 m n p).
Proof. exact (MK_COMB (@lem231261) (@lem231257 m n p)). Qed.
Lemma lem231263 (p : nat) (m : nat) (n : nat) : (term230 p m n) = (term230 p m n).
Proof. exact (eq_refl (term230 p m n)). Qed.
Lemma lem231264 (p : nat) (m : nat) (n : nat) : (term609 p m n) = (term612 p m n).
Proof. exact (MK_COMB (@lem231262 m n p) (@lem231263 p m n)). Qed.
Lemma lem231265 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem231266 (p : nat) (m : nat) (n : nat) : (m = (term609 p m n)) = (m = (term612 p m n)).
Proof. exact (MK_COMB (@lem231265 m) (@lem231264 p m n)). Qed.
Lemma lem231269 (p : nat) (m : nat) (n : nat) : (m = (term612 p m n)) = (m = (term609 p m n)).
Proof. exact (SYM (@lem231266 p m n)). Qed.
Lemma lem231273 (m : nat) (n : nat) (p : nat) : (term46 m n p) = (term47 m n p).
Proof. exact (EQ_MP (@lem227473 m n p) (@lem227472 m n p)). Qed.
Lemma lem231274 (p : nat) (m : nat) (n : nat) : (term612 p m n) = (term613 p m n).
Proof. exact (@lem231273 (term610 m n p) (term226 m n p) (Nat.modulo m n)). Qed.
Lemma lem231276 (m : nat) (n : nat) (p : nat) : (term25 n m p) = (term24 m n p).
Proof. exact (EQ_MP (@lem227482 m n p) (@lem227481 m n p)). Qed.
Lemma lem231277 (m : nat) (n : nat) (p : nat) : (term614 m n p) = (term615 m n p).
Proof. exact (@lem231276 n (term616 m n p) (term224 m n p)). Qed.
Lemma lem231279 (m : nat) (n : nat) (p : nat) : (term11 m n p) = (term10 m n p).
Proof. exact (EQ_MP (@lem227464 m n p) (@lem227463 m n p)). Qed.
Lemma lem231280 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem231281 (m : nat) (n : nat) (p : nat) : (term600 m n p) = (term599 m n p).
Proof. exact (MK_COMB (@lem231280) (@lem231279 m n p)). Qed.
Lemma lem231282 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem231283 (m : nat) (n : nat) (p : nat) : (term616 m n p) = (term617 m n p).
Proof. exact (MK_COMB (@lem231281 m n p) (@lem231282 p)). Qed.
Lemma lem231284 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem231285 (m : nat) (n : nat) (p : nat) : (term618 m n p) = (term619 m n p).
Proof. exact (MK_COMB (@lem231284) (@lem231283 m n p)). Qed.
Lemma lem231286 (m : nat) (n : nat) (p : nat) : (term224 m n p) = (term224 m n p).
Proof. exact (eq_refl (term224 m n p)). Qed.
Lemma lem231287 (m : nat) (n : nat) (p : nat) : (term620 m n p) = (term621 m n p).
Proof. exact (MK_COMB (@lem231285 m n p) (@lem231286 m n p)). Qed.
Lemma lem231288 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem231289 (m : nat) (n : nat) (p : nat) : (term615 m n p) = (term622 m n p).
Proof. exact (MK_COMB (@lem231288 n) (@lem231287 m n p)). Qed.
Lemma lem231290 (m : nat) (n : nat) (p : nat) : (term614 m n p) = (term622 m n p).
Proof. exact (TRANS (@lem231277 m n p) (@lem231289 m n p)). Qed.
Lemma lem231291 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem231292 (m : nat) (n : nat) (p : nat) : (term623 m n p) = (term624 m n p).
Proof. exact (MK_COMB (@lem231291) (@lem231290 m n p)). Qed.
Lemma lem231293 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem231294 (p : nat) (m : nat) (n : nat) : (term613 p m n) = (term625 p m n).
Proof. exact (MK_COMB (@lem231292 m n p) (@lem231293 m n)). Qed.
Lemma lem231295 (p : nat) (m : nat) (n : nat) : (term612 p m n) = (term625 p m n).
Proof. exact (TRANS (@lem231274 p m n) (@lem231294 p m n)). Qed.
Lemma lem231296 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem231297 (p : nat) (m : nat) (n : nat) : (m = (term612 p m n)) = (m = (term625 p m n)).
Proof. exact (MK_COMB (@lem231296 m) (@lem231295 p m n)). Qed.
Lemma lem231300 (p : nat) (m : nat) (n : nat) : (m = (term625 p m n)) = (m = (term612 p m n)).
Proof. exact (SYM (@lem231297 p m n)). Qed.
Lemma lem231304 (n : nat) (m : nat) : (term9 m n) = m.
Proof. exact (EQ_MP (@lem227419 n m) (@lem227418 m n)). Qed.
Lemma lem231305 (p : nat) (m : nat) (n : nat) : (term621 m n p) = (Nat.div m n).
Proof. exact (@lem231304 p (Nat.div m n)). Qed.
Lemma lem231306 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem231307 (p : nat) (m : nat) (n : nat) : (term622 m n p) = (term236 m n).
Proof. exact (MK_COMB (@lem231306 n) (@lem231305 p m n)). Qed.
Lemma lem231308 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem231309 (p : nat) (m : nat) (n : nat) : (term624 m n p) = (term237 m n).
Proof. exact (MK_COMB (@lem231308) (@lem231307 p m n)). Qed.
Lemma lem231310 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (eq_refl (Nat.modulo m n)). Qed.
Lemma lem231311 (p : nat) (m : nat) (n : nat) : (term625 p m n) = (term4 m n).
Proof. exact (MK_COMB (@lem231309 p m n) (@lem231310 m n)). Qed.
Lemma lem231313 (n : nat) (m : nat) : (term4 m n) = m.
Proof. exact (EQ_MP (@lem227412 n m) (@lem227411 m n)). Qed.
Lemma lem231314 (p : nat) (n : nat) (m : nat) : (term625 p m n) = m.
Proof. exact (TRANS (@lem231311 p m n) (@lem231313 n m)). Qed.
Lemma lem231315 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem231316 (p : nat) (n : nat) (m : nat) : (m = (term625 p m n)) = (m = m).
Proof. exact (MK_COMB (@lem231315 m) (@lem231314 p n m)). Qed.
Lemma lem231318 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem231319 (x : nat) : (x = x) = True.
Proof. exact (@lem231318 nat x). Qed.
Lemma lem231320 (m : nat) : (m = m) = True.
Proof. exact (@lem231319 m). Qed.
Lemma lem231321 (p : nat) (m : nat) (n : nat) : (m = (term625 p m n)) = True.
Proof. exact (TRANS (@lem231316 p n m) (@lem231320 m)). Qed.
Lemma lem231322 (p : nat) (m : nat) (n : nat) : True = (m = (term625 p m n)).
Proof. exact (SYM (@lem231321 p m n)). Qed.
Lemma lem231323 (p : nat) (m : nat) (n : nat) : m = (term625 p m n).
Proof. exact (EQ_MP (@lem231322 p m n) (@lem0)). Qed.
Lemma lem231324 (p : nat) (m : nat) (n : nat) : m = (term612 p m n).
Proof. exact (EQ_MP (@lem231300 p m n) (@lem231323 p m n)). Qed.
Lemma lem231325 (p : nat) (m : nat) (n : nat) : m = (term609 p m n).
Proof. exact (EQ_MP (@lem231269 p m n) (@lem231324 p m n)). Qed.
Lemma lem231326 (p : nat) (m : nat) (n : nat) : (term605 m n p) = (term608 p m n).
Proof. exact (EQ_MP (@lem231252 p m n) (@lem231325 p m n)). Qed.
Lemma lem231327 (p : nat) (m : nat) (n : nat) : term626 p m n.
Proof. exact (ex_intro (term627 p m n) (term601 m n p) (@lem231326 p m n)). Qed.
Lemma lem231328 (p : nat) (m : nat) (n : nat) : (term219 m n p) = (term230 p m n).
Proof. exact (@lem231218 p m n (@lem231327 p m n)). Qed.
Lemma lem231330 (p : nat) (m : nat) (n : nat) (h1 : term209 n) : (term219 m n p) = (term230 p m n).
Proof. exact (or_elim (@lem228519 p) (fun h0 : p = (NUMERAL 0) => @lem231215 m n p h1 h0) (fun h0 : term209 p => @lem231328 p m n)). Qed.
Lemma lem231331 (p : nat) (m : nat) (n : nat) : (term219 m n p) = (term230 p m n).
Proof. exact (or_elim (@lem228524 n) (fun h0 : n = (NUMERAL 0) => @lem228647 p m n h0) (fun h0 : term209 n => @lem231330 p m n h0)). Qed.
Lemma lem231336 (m : nat) (n : nat) : term628 m n.
Proof. exact (fun p : nat => @lem231331 p m n). Qed.
Lemma lem231341 (m : nat) : term629 m.
Proof. exact (fun n : nat => @lem231336 m n). Qed.
Lemma lem231346 : term630.
Proof. exact (fun m : nat => @lem231341 m). Qed.
