Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm161350_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import MULT_SYM_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm159136_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
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
Require Import thm69_spec.
Lemma lem160346 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem160347 (n : nat) (m : nat) : ((term1 m n) = m) = (term2 n m).
Proof. exact (@lem160346 ((term1 m n) = m)). Qed.
Lemma lem160348 (n : nat) (m : nat) : (term2 n m) = ((term1 m n) = m).
Proof. exact (SYM (@lem160347 n m)). Qed.
Lemma lem160349 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem160352 (n : nat) (m : nat) (h1 : term4 n m) : term4 n m.
Proof. exact (h1). Qed.
Lemma lem160353 (n : nat) (m : nat) : term5 n m.
Proof. exact (fun h0 : term4 n m => @lem160352 n m h0). Qed.
Lemma lem160354 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (h1). Qed.
Lemma lem160355 (n : nat) (m : nat) (h1 : term4 n m) : term4 n m.
Proof. exact (h1). Qed.
Lemma lem160356 (n : nat) (m : nat) (h1 : term4 n m) (h2 : term5 n m) : term4 n m.
Proof. exact (@lem160354 n m h2 (@lem160355 n m h1)). Qed.
Lemma lem160357 (n : nat) (m : nat) (h1 : term4 n m) : term6 n m.
Proof. exact (fun h0 : term5 n m => @lem160356 n m h1 h0). Qed.
Lemma lem160358 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (h1). Qed.
Lemma lem160359 (n : nat) (m : nat) (h1 : term4 n m) (h2 : term5 n m) : term4 n m.
Proof. exact (@lem160357 n m h1 (@lem160358 n m h2)). Qed.
Lemma lem160360 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (fun h0 : term4 n m => @lem160359 n m h0 h1). Qed.
Lemma lem160361 (n : nat) (m : nat) : term7 n m.
Proof. exact (fun h0 : term5 n m => @lem160360 n m h0). Qed.
Lemma lem160364 (n : nat) (m : nat) : term5 n m.
Proof. exact (@lem160361 n m (@lem160353 n m)). Qed.
Lemma lem160388 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem160389 : term8 = term9.
Proof. exact (@lem160388 term10). Qed.
Lemma lem160402 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem160403 : term12 = term13.
Proof. exact (MK_COMB (@lem160402) (@lem160389)). Qed.
Lemma lem160406 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem160407 (n : nat) (m : nat) : (term15 n m) = (term16 n m).
Proof. exact (MK_COMB (@lem160406 n m) (@lem160403)). Qed.
Lemma lem160410 (n : nat) : (term17 n) = (term17 n).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem160411 (n : nat) (m : nat) : (term4 n m) = (term18 n m).
Proof. exact (MK_COMB (@lem160410 n) (@lem160407 n m)). Qed.
Lemma lem160414 (m : nat) : (term19 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem160411 n m)). Qed.
Lemma lem160415 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160416 (m : nat) : (term21 m) = (term22 m).
Proof. exact (MK_COMB (@lem160415) (@lem160414 m)). Qed.
Lemma lem160421 : term23 = term24.
Proof. exact (fun_ext (fun m : nat => @lem160416 m)). Qed.
Lemma lem160422 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160431 : term25 = term26.
Proof. exact (MK_COMB (@lem160422) (@lem160421)). Qed.
Lemma lem160442 (m : nat) (n : nat) : (term27 m n) = (term27 m n).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem160443 (m : nat) : (term28 m) = (term28 m).
Proof. exact (fun_ext (fun n : nat => @lem160442 m n)). Qed.
Lemma lem160444 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160445 (m : nat) : (term29 m) = (term29 m).
Proof. exact (MK_COMB (@lem160444) (@lem160443 m)). Qed.
Lemma lem160446 : term30 = term30.
Proof. exact (fun_ext (fun m : nat => @lem160445 m)). Qed.
Lemma lem160447 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160448 : term10 = term10.
Proof. exact (MK_COMB (@lem160447) (@lem160446)). Qed.
Lemma lem160449 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem160450 : term9 = term9.
Proof. exact (MK_COMB (@lem160449) (@lem160448)). Qed.
Lemma lem160451 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem160452 (m : nat) : (term31 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem160451 n m)). Qed.
Lemma lem160453 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160454 (m : nat) : (term32 m) = (term32 m).
Proof. exact (MK_COMB (@lem160453) (@lem160452 m)). Qed.
Lemma lem160455 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem160454 m)). Qed.
Lemma lem160456 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160457 : term34 = term34.
Proof. exact (MK_COMB (@lem160456) (@lem160455)). Qed.
Lemma lem160458 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem160459 : term11 = term11.
Proof. exact (MK_COMB (@lem160458) (@lem160457)). Qed.
Lemma lem160460 : term13 = term13.
Proof. exact (MK_COMB (@lem160459) (@lem160450)). Qed.
Lemma lem160465 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem160466 (n : nat) (m : nat) : (term16 n m) = (term16 n m).
Proof. exact (MK_COMB (@lem160465 n m) (@lem160460)). Qed.
Lemma lem160471 (n : nat) : (term17 n) = (term17 n).
Proof. exact (eq_refl (term17 n)). Qed.
Lemma lem160472 (n : nat) (m : nat) : (term18 n m) = (term18 n m).
Proof. exact (MK_COMB (@lem160471 n) (@lem160466 n m)). Qed.
Lemma lem160473 (m : nat) : (term20 m) = (term20 m).
Proof. exact (fun_ext (fun n : nat => @lem160472 n m)). Qed.
Lemma lem160474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160475 (m : nat) : (term22 m) = (term22 m).
Proof. exact (MK_COMB (@lem160474) (@lem160473 m)). Qed.
Lemma lem160476 : term24 = term24.
Proof. exact (fun_ext (fun m : nat => @lem160475 m)). Qed.
Lemma lem160477 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160478 : term26 = term26.
Proof. exact (MK_COMB (@lem160477) (@lem160476)). Qed.
Lemma lem160527 : term25 = term26.
Proof. exact (TRANS (@lem160431) (@lem160478)). Qed.
Lemma lem160528 : term26 = term25.
Proof. exact (SYM (@lem160527)). Qed.
Lemma lem160531 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem160532 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem160538 (n : nat) (h1 : term35 n) : term35 n.
Proof. exact (h1). Qed.
Lemma lem160544 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem160545 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem160546 (m : nat) : (term31 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem160545 n m)). Qed.
Lemma lem160547 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160548 (m : nat) : (term32 m) = (term32 m).
Proof. exact (MK_COMB (@lem160547) (@lem160546 m)). Qed.
Lemma lem160549 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem160548 m)). Qed.
Lemma lem160550 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160563 : term34 = term34.
Proof. exact (MK_COMB (@lem160550) (@lem160549)). Qed.
Lemma lem160564 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem160563) (@lem160531 h1)). Qed.
Lemma lem160567 (n : nat) : (term36 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem160572 (m : nat) (n : nat) : (term37 m n) = (term37 m n).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem160573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem160574 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem160573) (@lem160567 n)). Qed.
Lemma lem160575 (m : nat) (n : nat) : (term40 m n) = (term41 m n).
Proof. exact (MK_COMB (@lem160574 n) (@lem160572 m n)). Qed.
Lemma lem160576 (m : nat) (n : nat) : (term27 m n) = (term40 m n).
Proof. exact (@lem17265 (term35 n) (term37 m n)). Qed.
Lemma lem160577 (m : nat) (n : nat) : (term27 m n) = (term41 m n).
Proof. exact (TRANS (@lem160576 m n) (@lem160575 m n)). Qed.
Lemma lem160578 (m : nat) : (term28 m) = (term42 m).
Proof. exact (fun_ext (fun n : nat => @lem160577 m n)). Qed.
Lemma lem160579 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160580 (m : nat) : (term29 m) = (term43 m).
Proof. exact (MK_COMB (@lem160579) (@lem160578 m)). Qed.
Lemma lem160581 : term30 = term44.
Proof. exact (fun_ext (fun m : nat => @lem160580 m)). Qed.
Lemma lem160582 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160639 : term10 = term45.
Proof. exact (MK_COMB (@lem160582) (@lem160581)). Qed.
Lemma lem160640 (h1 : term10) : term45.
Proof. exact (EQ_MP (@lem160639) (@lem160532 h1)). Qed.
Lemma lem160650 (n : nat) (h1 : term35 n) : term35 n.
Proof. exact (h1). Qed.
Lemma lem160674 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem160687 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem160688 (m : nat) : (term31 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem160687 n m)). Qed.
Lemma lem160689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160690 (m : nat) : (term32 m) = (term32 m).
Proof. exact (MK_COMB (@lem160689) (@lem160688 m)). Qed.
Lemma lem160691 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem160690 m)). Qed.
Lemma lem160692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160693 : term34 = term34.
Proof. exact (MK_COMB (@lem160692) (@lem160691)). Qed.
Lemma lem160694 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem160693) (@lem160564 h1)). Qed.
Lemma lem160737 (m : nat) (n : nat) : (term41 m n) = (term41 m n).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem160738 (m : nat) : (term42 m) = (term42 m).
Proof. exact (fun_ext (fun n : nat => @lem160737 m n)). Qed.
Lemma lem160739 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160740 (m : nat) : (term43 m) = (term43 m).
Proof. exact (MK_COMB (@lem160739) (@lem160738 m)). Qed.
Lemma lem160741 : term44 = term44.
Proof. exact (fun_ext (fun m : nat => @lem160740 m)). Qed.
Lemma lem160742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160743 : term45 = term45.
Proof. exact (MK_COMB (@lem160742) (@lem160741)). Qed.
Lemma lem160744 (h1 : term10) : term45.
Proof. exact (EQ_MP (@lem160743) (@lem160640 h1)). Qed.
Lemma lem160748 (n : nat) (h1 : term35 n) : term35 n.
Proof. exact (h1). Qed.
Lemma lem160752 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem160754 (n : nat) (m : nat) : ((Nat.mul m n) = (Nat.mul n m)) = ((Nat.mul m n) = (Nat.mul n m)).
Proof. exact (eq_refl ((Nat.mul m n) = (Nat.mul n m))). Qed.
Lemma lem160755 (m : nat) : (term31 m) = (term31 m).
Proof. exact (fun_ext (fun n : nat => @lem160754 n m)). Qed.
Lemma lem160756 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160757 (m : nat) : (term32 m) = (term32 m).
Proof. exact (MK_COMB (@lem160756) (@lem160755 m)). Qed.
Lemma lem160758 : term33 = term33.
Proof. exact (fun_ext (fun m : nat => @lem160757 m)). Qed.
Lemma lem160759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160761 : term34 = term34.
Proof. exact (MK_COMB (@lem160759) (@lem160758)). Qed.
Lemma lem160762 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem160761) (@lem160694 h1)). Qed.
Lemma lem160780 (m : nat) (n : nat) : (term41 m n) = (term46 m n).
Proof. exact (@lem19490 (m = (term47 m n)) (n = (NUMERAL 0)) (term48 m n)). Qed.
Lemma lem160781 (m : nat) : (term42 m) = (term49 m).
Proof. exact (fun_ext (fun n : nat => @lem160780 m n)). Qed.
Lemma lem160782 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160783 (m : nat) : (term43 m) = (term50 m).
Proof. exact (MK_COMB (@lem160782) (@lem160781 m)). Qed.
Lemma lem160784 : term44 = term51.
Proof. exact (fun_ext (fun m : nat => @lem160783 m)). Qed.
Lemma lem160785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem160787 : term45 = term52.
Proof. exact (MK_COMB (@lem160785) (@lem160784)). Qed.
Lemma lem160788 (h1 : term10) : term52.
Proof. exact (EQ_MP (@lem160787) (@lem160744 h1)). Qed.
Lemma lem160789 (_3218 : nat) (h1 : term34) : term53 _3218.
Proof. exact (@lem160762 h1 _3218). Qed.
Lemma lem160790 (_3218 : nat) : (term53 _3218) = (term32 _3218).
Proof. exact (eq_refl (term53 _3218)). Qed.
Lemma lem160791 (_3218 : nat) (h1 : term34) : term32 _3218.
Proof. exact (EQ_MP (@lem160790 _3218) (@lem160789 _3218 h1)). Qed.
Lemma lem160792 (_3218 : nat) (_3219 : nat) (h1 : term34) : term54 _3218 _3219.
Proof. exact (@lem160791 _3218 h1 _3219). Qed.
Lemma lem160793 (_3219 : nat) (_3218 : nat) : (term54 _3218 _3219) = ((Nat.mul _3218 _3219) = (Nat.mul _3219 _3218)).
Proof. exact (eq_refl (term54 _3218 _3219)). Qed.
Lemma lem160795 (_3220 : nat) (h1 : term10) : term55 _3220.
Proof. exact (@lem160788 h1 _3220). Qed.
Lemma lem160796 (_3220 : nat) : (term55 _3220) = (term50 _3220).
Proof. exact (eq_refl (term55 _3220)). Qed.
Lemma lem160797 (_3220 : nat) (h1 : term10) : term50 _3220.
Proof. exact (EQ_MP (@lem160796 _3220) (@lem160795 _3220 h1)). Qed.
Lemma lem160798 (_3220 : nat) (_3221 : nat) (h1 : term10) : term56 _3220 _3221.
Proof. exact (@lem160797 _3220 h1 _3221). Qed.
Lemma lem160799 (_3220 : nat) (_3221 : nat) : (term56 _3220 _3221) = (term46 _3220 _3221).
Proof. exact (eq_refl (term56 _3220 _3221)). Qed.
Lemma lem160800 (_3220 : nat) (_3221 : nat) (h1 : term10) : term46 _3220 _3221.
Proof. exact (EQ_MP (@lem160799 _3220 _3221) (@lem160798 _3220 _3221 h1)). Qed.
Lemma lem160804 (n : nat) (h1 : term35 n) : term35 n.
Proof. exact (h1). Qed.
Lemma lem160806 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem160814 (_3220 : nat) (_3221 : nat) (h1 : term10) : term57 _3220 _3221.
Proof. exact (proj1 (@lem160800 _3220 _3221 h1)). Qed.
Lemma lem160885 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem160886 (_3238 : nat) (_3240 : nat) (h1 : _3238 = _3240) : _3238 = _3240.
Proof. exact (h1). Qed.
Lemma lem160887 (_3239 : nat) (_3241 : nat) (h1 : _3239 = _3241) : _3239 = _3241.
Proof. exact (h1). Qed.
Lemma lem160888 (_3238 : nat) (_3240 : nat) (h1 : _3238 = _3240) : (Nat.add _3238) = (Nat.add _3240).
Proof. exact (MK_COMB (@lem160885) (@lem160886 _3238 _3240 h1)). Qed.
Lemma lem160889 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) (h1 : _3238 = _3240) (h2 : _3239 = _3241) : (Nat.add _3238 _3239) = (Nat.add _3240 _3241).
Proof. exact (MK_COMB (@lem160888 _3238 _3240 h1) (@lem160887 _3239 _3241 h2)). Qed.
Lemma lem160890 (_3239 : nat) (_3241 : nat) (_3238 : nat) (_3240 : nat) (h1 : _3238 = _3240) : term58 _3238 _3239 _3240 _3241.
Proof. exact (fun h0 : _3239 = _3241 => @lem160889 _3238 _3240 _3239 _3241 h1 h0). Qed.
Lemma lem160892 (a : Prop) (b : Prop) : (a -> b) = (term59 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem160893 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : (term58 _3238 _3239 _3240 _3241) = (term60 _3238 _3239 _3240 _3241).
Proof. exact (@lem160892 (_3239 = _3241) ((Nat.add _3238 _3239) = (Nat.add _3240 _3241))). Qed.
Lemma lem160894 (_3239 : nat) (_3241 : nat) (_3238 : nat) (_3240 : nat) (h1 : _3238 = _3240) : term60 _3238 _3239 _3240 _3241.
Proof. exact (EQ_MP (@lem160893 _3238 _3239 _3240 _3241) (@lem160890 _3239 _3241 _3238 _3240 h1)). Qed.
Lemma lem160895 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : term61 _3238 _3239 _3240 _3241.
Proof. exact (fun h0 : _3238 = _3240 => @lem160894 _3239 _3241 _3238 _3240 h0). Qed.
Lemma lem160897 (a : Prop) (b : Prop) : (a -> b) = (term59 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem160898 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : (term61 _3238 _3239 _3240 _3241) = (term62 _3238 _3239 _3240 _3241).
Proof. exact (@lem160897 (_3238 = _3240) (term60 _3238 _3239 _3240 _3241)). Qed.
Lemma lem160899 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : term62 _3238 _3239 _3240 _3241.
Proof. exact (EQ_MP (@lem160898 _3238 _3239 _3240 _3241) (@lem160895 _3238 _3239 _3240 _3241)). Qed.
Lemma lem160909 (x : nat) (y : nat) (z : nat) : term63 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem160911 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem160912 (m : nat) : m = m.
Proof. exact (@lem160911 m). Qed.
Lemma lem160913 (m : nat) : term64 m.
Proof. exact (fun h0 : term65 m => @lem160912 m). Qed.
Lemma lem160915 (p : Prop) : (term66 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160916 (m : nat) : (term64 m) = (m = m).
Proof. exact (@lem160915 (m = m)). Qed.
Lemma lem160917 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem160916 m) (@lem160913 m)). Qed.
Lemma lem160919 (_3219 : nat) (_3218 : nat) (h1 : term34) : (Nat.mul _3218 _3219) = (Nat.mul _3219 _3218).
Proof. exact (EQ_MP (@lem160793 _3219 _3218) (@lem160792 _3218 _3219 h1)). Qed.
Lemma lem160920 (m : nat) (n : nat) (h1 : term34) : (term67 m n) = (term68 m n).
Proof. exact (@lem160919 n (Nat.div m n) h1). Qed.
Lemma lem160921 (m : nat) (n : nat) (h1 : term34) : term69 m n.
Proof. exact (fun h0 : term70 m n => @lem160920 m n h1). Qed.
Lemma lem160923 (p : Prop) : (term66 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160924 (m : nat) (n : nat) : (term69 m n) = ((term67 m n) = (term68 m n)).
Proof. exact (@lem160923 ((term67 m n) = (term68 m n))). Qed.
Lemma lem160925 (m : nat) (n : nat) (h1 : term34) : (term67 m n) = (term68 m n).
Proof. exact (EQ_MP (@lem160924 m n) (@lem160921 m n h1)). Qed.
Lemma lem160927 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem160928 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (@lem160927 (Nat.modulo m n)). Qed.
Lemma lem160929 (m : nat) (n : nat) : term71 m n.
Proof. exact (fun h0 : term72 m n => @lem160928 m n). Qed.
Lemma lem160931 (p : Prop) : (term66 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem160932 (m : nat) (n : nat) : (term71 m n) = ((Nat.modulo m n) = (Nat.modulo m n)).
Proof. exact (@lem160931 ((Nat.modulo m n) = (Nat.modulo m n))). Qed.
Lemma lem160933 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem160932 m n) (@lem160929 m n)). Qed.
Lemma lem160951 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem160952 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term60 _3238 _3239 _3240 _3241) = (term73 _3238 _3240 _3239 _3241).
Proof. exact (@lem160951 ((Nat.add _3238 _3239) = (Nat.add _3240 _3241)) (term74 _3239 _3241)). Qed.
Lemma lem160962 (_3238 : nat) (_3240 : nat) : (term75 _3238 _3240) = (term75 _3238 _3240).
Proof. exact (eq_refl (term75 _3238 _3240)). Qed.
Lemma lem160963 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term62 _3238 _3239 _3240 _3241) = (term76 _3238 _3240 _3239 _3241).
Proof. exact (MK_COMB (@lem160962 _3238 _3240) (@lem160952 _3238 _3240 _3239 _3241)). Qed.
Lemma lem160967 (q : Prop) (p : Prop) (r : Prop) : (term77 p q r) = (term77 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem160968 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term76 _3238 _3240 _3239 _3241) = (term78 _3238 _3240 _3239 _3241).
Proof. exact (@lem160967 ((Nat.add _3238 _3239) = (Nat.add _3240 _3241)) (term74 _3238 _3240) (term74 _3239 _3241)). Qed.
Lemma lem160990 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term62 _3238 _3239 _3240 _3241) = (term78 _3238 _3240 _3239 _3241).
Proof. exact (TRANS (@lem160963 _3238 _3240 _3239 _3241) (@lem160968 _3238 _3240 _3239 _3241)). Qed.
Lemma lem160991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem160992 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term79 _3238 _3239 _3240 _3241) = (term80 _3238 _3240 _3239 _3241).
Proof. exact (MK_COMB (@lem160991) (@lem160990 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161014 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term78 _3238 _3240 _3239 _3241) = (term78 _3238 _3240 _3239 _3241).
Proof. exact (eq_refl (term78 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161015 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : ((term62 _3238 _3239 _3240 _3241) = (term78 _3238 _3240 _3239 _3241)) = ((term78 _3238 _3240 _3239 _3241) = (term78 _3238 _3240 _3239 _3241)).
Proof. exact (MK_COMB (@lem160992 _3238 _3240 _3239 _3241) (@lem161014 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161017 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem161018 (x : Prop) : (x = x) = True.
Proof. exact (@lem161017 Prop x). Qed.
Lemma lem161019 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : ((term78 _3238 _3240 _3239 _3241) = (term78 _3238 _3240 _3239 _3241)) = True.
Proof. exact (@lem161018 (term78 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161020 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : ((term62 _3238 _3239 _3240 _3241) = (term78 _3238 _3240 _3239 _3241)) = True.
Proof. exact (TRANS (@lem161015 _3238 _3240 _3239 _3241) (@lem161019 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161021 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : True = ((term62 _3238 _3239 _3240 _3241) = (term78 _3238 _3240 _3239 _3241)).
Proof. exact (SYM (@lem161020 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161022 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term62 _3238 _3239 _3240 _3241) = (term78 _3238 _3240 _3239 _3241).
Proof. exact (EQ_MP (@lem161021 _3238 _3240 _3239 _3241) (@lem0)). Qed.
Lemma lem161023 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : term78 _3238 _3240 _3239 _3241.
Proof. exact (EQ_MP (@lem161022 _3238 _3240 _3239 _3241) (@lem160899 _3238 _3239 _3240 _3241)). Qed.
Lemma lem161025 (b : Prop) (a : Prop) : (a \/ b) = (term81 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem161026 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : (term78 _3238 _3240 _3239 _3241) = (term82 _3238 _3239 _3240 _3241).
Proof. exact (@lem161025 (term83 _3238 _3240 _3239 _3241) ((Nat.add _3238 _3239) = (Nat.add _3240 _3241))). Qed.
Lemma lem161028 (a : Prop) (b : Prop) : (term84 a b) = (term85 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem161029 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term86 _3238 _3240 _3239 _3241) = (term87 _3238 _3240 _3239 _3241).
Proof. exact (@lem161028 (term74 _3238 _3240) (term74 _3239 _3241)). Qed.
Lemma lem161031 (a : Prop) : (term88 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem161032 (_3238 : nat) (_3240 : nat) : (term89 _3238 _3240) = (_3238 = _3240).
Proof. exact (@lem161031 (_3238 = _3240)). Qed.
Lemma lem161033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem161034 (_3238 : nat) (_3240 : nat) : (term90 _3238 _3240) = (term91 _3238 _3240).
Proof. exact (MK_COMB (@lem161033) (@lem161032 _3238 _3240)). Qed.
Lemma lem161036 (a : Prop) : (term88 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem161037 (_3239 : nat) (_3241 : nat) : (term89 _3239 _3241) = (_3239 = _3241).
Proof. exact (@lem161036 (_3239 = _3241)). Qed.
Lemma lem161038 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term87 _3238 _3240 _3239 _3241) = (term92 _3238 _3240 _3239 _3241).
Proof. exact (MK_COMB (@lem161034 _3238 _3240) (@lem161037 _3239 _3241)). Qed.
Lemma lem161039 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term86 _3238 _3240 _3239 _3241) = (term92 _3238 _3240 _3239 _3241).
Proof. exact (TRANS (@lem161029 _3238 _3240 _3239 _3241) (@lem161038 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem161041 (_3238 : nat) (_3240 : nat) (_3239 : nat) (_3241 : nat) : (term93 _3238 _3240 _3239 _3241) = (term94 _3238 _3240 _3239 _3241).
Proof. exact (MK_COMB (@lem161040) (@lem161039 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161042 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : ((Nat.add _3238 _3239) = (Nat.add _3240 _3241)) = ((Nat.add _3238 _3239) = (Nat.add _3240 _3241)).
Proof. exact (eq_refl ((Nat.add _3238 _3239) = (Nat.add _3240 _3241))). Qed.
Lemma lem161043 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : (term82 _3238 _3239 _3240 _3241) = (term95 _3238 _3239 _3240 _3241).
Proof. exact (MK_COMB (@lem161041 _3238 _3240 _3239 _3241) (@lem161042 _3238 _3239 _3240 _3241)). Qed.
Lemma lem161044 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : (term78 _3238 _3240 _3239 _3241) = (term95 _3238 _3239 _3240 _3241).
Proof. exact (TRANS (@lem161026 _3238 _3239 _3240 _3241) (@lem161043 _3238 _3239 _3240 _3241)). Qed.
Lemma lem161046 (m : nat) (n : nat) (h1 : term34) : term96 m n.
Proof. exact (conj (@lem160925 m n h1) (@lem160933 m n)). Qed.
Lemma lem161048 (_3238 : nat) (_3239 : nat) (_3240 : nat) (_3241 : nat) : term95 _3238 _3239 _3240 _3241.
Proof. exact (EQ_MP (@lem161044 _3238 _3239 _3240 _3241) (@lem161023 _3238 _3240 _3239 _3241)). Qed.
Lemma lem161049 (m : nat) (n : nat) : term97 m n.
Proof. exact (@lem161048 (term67 m n) (Nat.modulo m n) (term68 m n) (Nat.modulo m n)). Qed.
Lemma lem161052 (m : nat) (n : nat) (h1 : term34) : (term47 m n) = (term1 m n).
Proof. exact (@lem161049 m n (@lem161046 m n h1)). Qed.
Lemma lem161053 (m : nat) (n : nat) (h1 : term34) : term98 m n.
Proof. exact (fun h0 : term99 m n => @lem161052 m n h1). Qed.
Lemma lem161055 (p : Prop) : (term66 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem161056 (m : nat) (n : nat) : (term98 m n) = ((term47 m n) = (term1 m n)).
Proof. exact (@lem161055 ((term47 m n) = (term1 m n))). Qed.
Lemma lem161057 (m : nat) (n : nat) (h1 : term34) : (term47 m n) = (term1 m n).
Proof. exact (EQ_MP (@lem161056 m n) (@lem161053 m n h1)). Qed.
Lemma lem161059 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem161060 (n : nat) (m : nat) (h1 : term3 n m) : term100 n m.
Proof. exact (fun h0 : (term1 m n) = m => @lem161059 n m h1). Qed.
Lemma lem161062 (p : Prop) : (term101 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem161063 (n : nat) (m : nat) : (term100 n m) = (term3 n m).
Proof. exact (@lem161062 ((term1 m n) = m)). Qed.
Lemma lem161064 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (EQ_MP (@lem161063 n m) (@lem161060 n m h1)). Qed.
Lemma lem161082 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem161083 (y : nat) (x : nat) (z : nat) : (term102 x y z) = (term103 y x z).
Proof. exact (@lem161082 (y = z) (term74 x z)). Qed.
Lemma lem161093 (x : nat) (y : nat) : (term75 x y) = (term75 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem161094 (y : nat) (x : nat) (z : nat) : (term63 x y z) = (term104 y x z).
Proof. exact (MK_COMB (@lem161093 x y) (@lem161083 y x z)). Qed.
Lemma lem161098 (q : Prop) (p : Prop) (r : Prop) : (term77 p q r) = (term77 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem161099 (y : nat) (x : nat) (z : nat) : (term104 y x z) = (term105 y x z).
Proof. exact (@lem161098 (y = z) (term74 x y) (term74 x z)). Qed.
Lemma lem161121 (y : nat) (x : nat) (z : nat) : (term63 x y z) = (term105 y x z).
Proof. exact (TRANS (@lem161094 y x z) (@lem161099 y x z)). Qed.
Lemma lem161122 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem161123 (y : nat) (x : nat) (z : nat) : (term106 x y z) = (term107 y x z).
Proof. exact (MK_COMB (@lem161122) (@lem161121 y x z)). Qed.
Lemma lem161127 (q : Prop) (p : Prop) (r : Prop) : (term77 p q r) = (term77 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem161128 (x : nat) (y : nat) (z : nat) : (term108 x y z) = (term63 x y z).
Proof. exact (@lem161127 (term74 x y) (term74 x z) (y = z)). Qed.
Lemma lem161144 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem161145 (y : nat) (x : nat) (z : nat) : (term102 x y z) = (term103 y x z).
Proof. exact (@lem161144 (y = z) (term74 x z)). Qed.
Lemma lem161155 (x : nat) (y : nat) : (term75 x y) = (term75 x y).
Proof. exact (eq_refl (term75 x y)). Qed.
Lemma lem161156 (y : nat) (x : nat) (z : nat) : (term63 x y z) = (term104 y x z).
Proof. exact (MK_COMB (@lem161155 x y) (@lem161145 y x z)). Qed.
Lemma lem161160 (q : Prop) (p : Prop) (r : Prop) : (term77 p q r) = (term77 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem161161 (y : nat) (x : nat) (z : nat) : (term104 y x z) = (term105 y x z).
Proof. exact (@lem161160 (y = z) (term74 x y) (term74 x z)). Qed.
Lemma lem161183 (y : nat) (x : nat) (z : nat) : (term63 x y z) = (term105 y x z).
Proof. exact (TRANS (@lem161156 y x z) (@lem161161 y x z)). Qed.
Lemma lem161184 (y : nat) (x : nat) (z : nat) : (term108 x y z) = (term105 y x z).
Proof. exact (TRANS (@lem161128 x y z) (@lem161183 y x z)). Qed.
Lemma lem161185 (y : nat) (x : nat) (z : nat) : ((term63 x y z) = (term108 x y z)) = ((term105 y x z) = (term105 y x z)).
Proof. exact (MK_COMB (@lem161123 y x z) (@lem161184 y x z)). Qed.
Lemma lem161187 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem161188 (x : Prop) : (x = x) = True.
Proof. exact (@lem161187 Prop x). Qed.
Lemma lem161189 (y : nat) (x : nat) (z : nat) : ((term105 y x z) = (term105 y x z)) = True.
Proof. exact (@lem161188 (term105 y x z)). Qed.
Lemma lem161190 (x : nat) (y : nat) (z : nat) : ((term63 x y z) = (term108 x y z)) = True.
Proof. exact (TRANS (@lem161185 y x z) (@lem161189 y x z)). Qed.
Lemma lem161191 (x : nat) (y : nat) (z : nat) : True = ((term63 x y z) = (term108 x y z)).
Proof. exact (SYM (@lem161190 x y z)). Qed.
Lemma lem161192 (x : nat) (y : nat) (z : nat) : (term63 x y z) = (term108 x y z).
Proof. exact (EQ_MP (@lem161191 x y z) (@lem0)). Qed.
Lemma lem161193 (x : nat) (y : nat) (z : nat) : term108 x y z.
Proof. exact (EQ_MP (@lem161192 x y z) (@lem160909 x y z)). Qed.
Lemma lem161195 (b : Prop) (a : Prop) : (a \/ b) = (term81 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem161196 (y : nat) (x : nat) (z : nat) : (term108 x y z) = (term109 y x z).
Proof. exact (@lem161195 (term110 x y z) (term74 x z)). Qed.
Lemma lem161198 (a : Prop) (b : Prop) : (term84 a b) = (term85 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem161199 (x : nat) (y : nat) (z : nat) : (term111 x y z) = (term112 x y z).
Proof. exact (@lem161198 (term74 x y) (y = z)). Qed.
Lemma lem161201 (a : Prop) : (term88 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem161202 (x : nat) (y : nat) : (term89 x y) = (x = y).
Proof. exact (@lem161201 (x = y)). Qed.
Lemma lem161203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem161204 (x : nat) (y : nat) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem161203) (@lem161202 x y)). Qed.
Lemma lem161205 (y : nat) (z : nat) : (term74 y z) = (term74 y z).
Proof. exact (eq_refl (term74 y z)). Qed.
Lemma lem161206 (x : nat) (y : nat) (z : nat) : (term112 x y z) = (term113 x y z).
Proof. exact (MK_COMB (@lem161204 x y) (@lem161205 y z)). Qed.
Lemma lem161207 (x : nat) (y : nat) (z : nat) : (term111 x y z) = (term113 x y z).
Proof. exact (TRANS (@lem161199 x y z) (@lem161206 x y z)). Qed.
Lemma lem161208 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem161209 (x : nat) (y : nat) (z : nat) : (term114 x y z) = (term115 x y z).
Proof. exact (MK_COMB (@lem161208) (@lem161207 x y z)). Qed.
Lemma lem161210 (x : nat) (z : nat) : (term74 x z) = (term74 x z).
Proof. exact (eq_refl (term74 x z)). Qed.
Lemma lem161211 (y : nat) (x : nat) (z : nat) : (term109 y x z) = (term116 y x z).
Proof. exact (MK_COMB (@lem161209 x y z) (@lem161210 x z)). Qed.
Lemma lem161212 (y : nat) (x : nat) (z : nat) : (term108 x y z) = (term116 y x z).
Proof. exact (TRANS (@lem161196 y x z) (@lem161211 y x z)). Qed.
Lemma lem161214 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term117 n m.
Proof. exact (conj (@lem161057 m n h1) (@lem161064 n m h2)). Qed.
Lemma lem161216 (y : nat) (x : nat) (z : nat) : term116 y x z.
Proof. exact (EQ_MP (@lem161212 y x z) (@lem161193 x y z)). Qed.
Lemma lem161217 (n : nat) (m : nat) : term118 n m.
Proof. exact (@lem161216 (term1 m n) (term47 m n) m). Qed.
Lemma lem161220 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term119 n m.
Proof. exact (@lem161217 n m (@lem161214 n m h1 h2)). Qed.
Lemma lem161221 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term120 n m.
Proof. exact (fun h0 : (term47 m n) = m => @lem161220 n m h1 h2). Qed.
Lemma lem161223 (p : Prop) : (term101 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem161224 (n : nat) (m : nat) : (term120 n m) = (term119 n m).
Proof. exact (@lem161223 ((term47 m n) = m)). Qed.
Lemma lem161225 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term119 n m.
Proof. exact (EQ_MP (@lem161224 n m) (@lem161221 n m h1 h2)). Qed.
Lemma lem161227 (b : Prop) (a : Prop) : (a \/ b) = (term81 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem161228 (z : nat) (x : nat) (y : nat) : (term63 x y z) = (term121 z x y).
Proof. exact (@lem161227 (term102 x y z) (term74 x y)). Qed.
Lemma lem161230 (a : Prop) (b : Prop) : (term84 a b) = (term85 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem161231 (x : nat) (y : nat) (z : nat) : (term122 x y z) = (term123 x y z).
Proof. exact (@lem161230 (term74 x z) (y = z)). Qed.
Lemma lem161233 (a : Prop) : (term88 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem161234 (x : nat) (z : nat) : (term89 x z) = (x = z).
Proof. exact (@lem161233 (x = z)). Qed.
Lemma lem161235 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem161236 (x : nat) (z : nat) : (term90 x z) = (term91 x z).
Proof. exact (MK_COMB (@lem161235) (@lem161234 x z)). Qed.
Lemma lem161237 (y : nat) (z : nat) : (term74 y z) = (term74 y z).
Proof. exact (eq_refl (term74 y z)). Qed.
Lemma lem161238 (x : nat) (y : nat) (z : nat) : (term123 x y z) = (term124 x y z).
Proof. exact (MK_COMB (@lem161236 x z) (@lem161237 y z)). Qed.
Lemma lem161239 (x : nat) (y : nat) (z : nat) : (term122 x y z) = (term124 x y z).
Proof. exact (TRANS (@lem161231 x y z) (@lem161238 x y z)). Qed.
Lemma lem161240 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem161241 (x : nat) (y : nat) (z : nat) : (term125 x y z) = (term126 x y z).
Proof. exact (MK_COMB (@lem161240) (@lem161239 x y z)). Qed.
Lemma lem161242 (x : nat) (y : nat) : (term74 x y) = (term74 x y).
Proof. exact (eq_refl (term74 x y)). Qed.
Lemma lem161243 (z : nat) (x : nat) (y : nat) : (term121 z x y) = (term127 z x y).
Proof. exact (MK_COMB (@lem161241 x y z) (@lem161242 x y)). Qed.
Lemma lem161244 (z : nat) (x : nat) (y : nat) : (term63 x y z) = (term127 z x y).
Proof. exact (TRANS (@lem161228 z x y) (@lem161243 z x y)). Qed.
Lemma lem161246 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term128 n m.
Proof. exact (conj (@lem160917 m) (@lem161225 n m h1 h2)). Qed.
Lemma lem161248 (z : nat) (x : nat) (y : nat) : term127 z x y.
Proof. exact (EQ_MP (@lem161244 z x y) (@lem160909 x y z)). Qed.
Lemma lem161249 (m : nat) (n : nat) : term129 m n.
Proof. exact (@lem161248 m m (term47 m n)). Qed.
Lemma lem161252 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term130 m n.
Proof. exact (@lem161249 m n (@lem161246 n m h1 h2)). Qed.
Lemma lem161253 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term131 m n.
Proof. exact (fun h0 : m = (term47 m n) => @lem161252 n m h1 h2). Qed.
Lemma lem161255 (p : Prop) : (term101 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem161256 (m : nat) (n : nat) : (term131 m n) = (term130 m n).
Proof. exact (@lem161255 (m = (term47 m n))). Qed.
Lemma lem161257 (n : nat) (m : nat) (h1 : term34) (h2 : term3 n m) : term130 m n.
Proof. exact (EQ_MP (@lem161256 m n) (@lem161253 n m h1 h2)). Qed.
Lemma lem161259 (b : Prop) (a : Prop) : (a \/ b) = (term81 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem161262 (_3220 : nat) (_3221 : nat) : (term57 _3220 _3221) = (term132 _3220 _3221).
Proof. exact (@lem161259 (_3220 = (term47 _3220 _3221)) (_3221 = (NUMERAL 0))). Qed.
Lemma lem161265 (_3220 : nat) (_3221 : nat) (h1 : term10) : term132 _3220 _3221.
Proof. exact (EQ_MP (@lem161262 _3220 _3221) (@lem160814 _3220 _3221 h1)). Qed.
Lemma lem161266 (m : nat) (n : nat) (h1 : term10) : term132 m n.
Proof. exact (@lem161265 m n h1). Qed.
Lemma lem161269 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term3 n m) : n = (NUMERAL 0).
Proof. exact (@lem161266 m n h2 (@lem161257 n m h1 h3)). Qed.
Lemma lem161270 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term3 n m) : term133 n.
Proof. exact (fun h0 : term35 n => @lem161269 n m h1 h2 h3). Qed.
Lemma lem161272 (p : Prop) : (term66 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem161273 (n : nat) : (term133 n) = (n = (NUMERAL 0)).
Proof. exact (@lem161272 (n = (NUMERAL 0))). Qed.
Lemma lem161274 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term3 n m) : n = (NUMERAL 0).
Proof. exact (EQ_MP (@lem161273 n) (@lem161270 n m h1 h2 h3)). Qed.
Lemma lem161277 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem161279 (n : nat) : (term35 n) = (term134 n).
Proof. exact (@lem161277 (n = (NUMERAL 0))). Qed.
Lemma lem161282 (n : nat) (h1 : term35 n) : term134 n.
Proof. exact (EQ_MP (@lem161279 n) (@lem160804 n h1)). Qed.
Lemma lem161285 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (@lem161282 n h3 (@lem161274 n m h1 h2 h4)). Qed.
Lemma lem161286 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : term135.
Proof. exact (fun h0 : ~ False => @lem161285 n m h1 h2 h3 h4). Qed.
Lemma lem161288 (p : Prop) : (term66 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem161289 : term135 = False.
Proof. exact (@lem161288 False). Qed.
Lemma lem161290 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161289) (@lem161286 n m h1 h2 h3 h4)). Qed.
Lemma lem161291 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h5 : term3 n m => @lem161290 n m h1 h2 h3 h4) (fun h5 : False => @lem160806 n m h4)). Qed.
Lemma lem161292 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161291 n m h1 h2 h3 h4) (@lem160806 n m h4)). Qed.
Lemma lem161293 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term35 n) = False.
Proof. exact (prop_ext (fun h5 : term35 n => @lem161292 n m h1 h2 h3 h4) (fun h5 : False => @lem160804 n h3)). Qed.
Lemma lem161294 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161293 n m h1 h2 h3 h4) (@lem160804 n h3)). Qed.
Lemma lem161295 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h5 : term3 n m => @lem161294 n m h1 h2 h3 h4) (fun h5 : False => @lem160752 n m h4)). Qed.
Lemma lem161296 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161295 n m h1 h2 h3 h4) (@lem160752 n m h4)). Qed.
Lemma lem161297 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term35 n) = False.
Proof. exact (prop_ext (fun h5 : term35 n => @lem161296 n m h1 h2 h3 h4) (fun h5 : False => @lem160748 n h3)). Qed.
Lemma lem161298 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161297 n m h1 h2 h3 h4) (@lem160748 n h3)). Qed.
Lemma lem161299 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem161298 n m h1 h2 h3 h4) (fun h5 : False => @lem160762 h1)). Qed.
Lemma lem161300 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161299 n m h1 h2 h3 h4) (@lem160762 h1)). Qed.
Lemma lem161301 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h5 : term3 n m => @lem161300 n m h1 h2 h3 h4) (fun h5 : False => @lem160752 n m h4)). Qed.
Lemma lem161302 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161301 n m h1 h2 h3 h4) (@lem160752 n m h4)). Qed.
Lemma lem161303 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term35 n) = False.
Proof. exact (prop_ext (fun h5 : term35 n => @lem161302 n m h1 h2 h3 h4) (fun h5 : False => @lem160748 n h3)). Qed.
Lemma lem161304 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161303 n m h1 h2 h3 h4) (@lem160748 n h3)). Qed.
Lemma lem161305 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem161304 n m h1 h2 h3 h4) (fun h5 : False => @lem160694 h1)). Qed.
Lemma lem161306 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161305 n m h1 h2 h3 h4) (@lem160694 h1)). Qed.
Lemma lem161307 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h5 : term3 n m => @lem161306 n m h1 h2 h3 h4) (fun h5 : False => @lem160674 n m h4)). Qed.
Lemma lem161308 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161307 n m h1 h2 h3 h4) (@lem160674 n m h4)). Qed.
Lemma lem161309 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term35 n) = False.
Proof. exact (prop_ext (fun h5 : term35 n => @lem161308 n m h1 h2 h3 h4) (fun h5 : False => @lem160650 n h3)). Qed.
Lemma lem161310 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161309 n m h1 h2 h3 h4) (@lem160650 n h3)). Qed.
Lemma lem161311 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : term34 = False.
Proof. exact (prop_ext (fun h5 : term34 => @lem161310 n m h1 h2 h3 h4) (fun h5 : False => @lem160564 h1)). Qed.
Lemma lem161312 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161311 n m h1 h2 h3 h4) (@lem160564 h1)). Qed.
Lemma lem161313 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h5 : term3 n m => @lem161312 n m h1 h2 h3 h4) (fun h5 : False => @lem160544 n m h4)). Qed.
Lemma lem161314 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161313 n m h1 h2 h3 h4) (@lem160544 n m h4)). Qed.
Lemma lem161315 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : (term35 n) = False.
Proof. exact (prop_ext (fun h5 : term35 n => @lem161314 n m h1 h2 h3 h4) (fun h5 : False => @lem160538 n h3)). Qed.
Lemma lem161316 (n : nat) (m : nat) (h1 : term34) (h2 : term10) (h3 : term35 n) (h4 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161315 n m h1 h2 h3 h4) (@lem160538 n h3)). Qed.
Lemma lem161317 (n : nat) (m : nat) (h1 : term34) (h2 : term35 n) (h3 : term3 n m) : term8.
Proof. exact (fun h0 : term10 => @lem161316 n m h1 h0 h2 h3). Qed.
Lemma lem161318 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem161319 (n : nat) (m : nat) (h1 : term34) (h2 : term35 n) (h3 : term3 n m) : term9.
Proof. exact (EQ_MP (@lem161318) (@lem161317 n m h1 h2 h3)). Qed.
Lemma lem161320 (n : nat) (m : nat) (h1 : term35 n) (h2 : term3 n m) : term13.
Proof. exact (fun h0 : term34 => @lem161319 n m h0 h1 h2). Qed.
Lemma lem161321 (m : nat) (n : nat) (h1 : term35 n) : term16 n m.
Proof. exact (fun h0 : term3 n m => @lem161320 n m h1 h0). Qed.
Lemma lem161322 (n : nat) (m : nat) : term18 n m.
Proof. exact (fun h0 : term35 n => @lem161321 m n h0). Qed.
Lemma lem161327 (m : nat) : term22 m.
Proof. exact (fun n : nat => @lem161322 n m). Qed.
Lemma lem161332 : term26.
Proof. exact (fun m : nat => @lem161327 m). Qed.
Lemma lem161333 : term25.
Proof. exact (EQ_MP (@lem160528) (@lem161332)). Qed.
Lemma lem161334 (m : nat) : term136 m.
Proof. exact (@lem161333 m). Qed.
Lemma lem161335 (m : nat) : (term136 m) = (term21 m).
Proof. exact (eq_refl (term136 m)). Qed.
Lemma lem161336 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem161335 m) (@lem161334 m)). Qed.
Lemma lem161337 (m : nat) (n : nat) : term137 m n.
Proof. exact (@lem161336 m n). Qed.
Lemma lem161338 (n : nat) (m : nat) : (term137 m n) = (term4 n m).
Proof. exact (eq_refl (term137 m n)). Qed.
Lemma lem161339 (n : nat) (m : nat) : term4 n m.
Proof. exact (EQ_MP (@lem161338 n m) (@lem161337 m n)). Qed.
Lemma lem161341 (n : nat) (m : nat) : term4 n m.
Proof. exact (@lem160364 n m (@lem161339 n m)). Qed.
Lemma lem161342 (m : nat) (n : nat) (h1 : term35 n) : term15 n m.
Proof. exact (@lem161341 n m (@lem159136 n h1)). Qed.
Lemma lem161343 (n : nat) (m : nat) (h1 : term35 n) (h2 : term3 n m) : term12.
Proof. exact (@lem161342 m n h1 (@lem160349 n m h2)). Qed.
Lemma lem161344 (n : nat) (m : nat) (h1 : term35 n) (h2 : term3 n m) : term8.
Proof. exact (@lem161343 n m h1 h2 (@lem81820)). Qed.
Lemma lem161345 (n : nat) (m : nat) (h1 : term35 n) (h2 : term3 n m) : False.
Proof. exact (@lem161344 n m h1 h2 (@lem157261)). Qed.
Lemma lem161346 (n : nat) (m : nat) (h1 : term35 n) (h2 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h3 : term3 n m => @lem161345 n m h1 h2) (fun h3 : False => @lem160349 n m h2)). Qed.
Lemma lem161347 (n : nat) (m : nat) (h1 : term35 n) (h2 : term3 n m) : False.
Proof. exact (EQ_MP (@lem161346 n m h1 h2) (@lem160349 n m h2)). Qed.
Lemma lem161348 (m : nat) (n : nat) (h1 : term35 n) : term2 n m.
Proof. exact (fun h0 : term3 n m => @lem161347 n m h1 h0). Qed.
Lemma lem161350 (m : nat) (n : nat) (h1 : term35 n) : (term1 m n) = m.
Proof. exact (EQ_MP (@lem160348 n m) (@lem161348 m n h1)). Qed.
