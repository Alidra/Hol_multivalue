Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_INF_APPROACH_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import HAS_INF_INF_spec.
Require Import INF_APPROACH_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem5305357 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem5305358 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem5305359 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem5305358 t1) (@lem5305357 t1)). Qed.
Lemma lem5305360 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem5305359 t1 t2). Qed.
Lemma lem5305361 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem5305362 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem5305361 t1 t2) (@lem5305360 t1 t2)). Qed.
Lemma lem5305363 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem5305362 t1 t2 t3). Qed.
Lemma lem5305364 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem5305365 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem5305364 t1 t2 t3) (@lem5305363 t1 t2 t3)). Qed.
Lemma lem5305366 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem5305365 t1 t2 t3)). Qed.
Lemma lem5305367 (s : real -> Prop) : term7 s.
Proof. exact (@lem5295254 s). Qed.
Lemma lem5305368 (s : real -> Prop) : (term7 s) = (term8 s).
Proof. exact (eq_refl (term7 s)). Qed.
Lemma lem5305369 (s : real -> Prop) : term8 s.
Proof. exact (EQ_MP (@lem5305368 s) (@lem5305367 s)). Qed.
Lemma lem5305370 (s : real -> Prop) (l : real) : term9 s l.
Proof. exact (@lem5305369 s l). Qed.
Lemma lem5305371 (s : real -> Prop) (l : real) : (term9 s l) = ((has_inf s l) = (term10 s l)).
Proof. exact (eq_refl (term9 s l)). Qed.
Lemma lem5305390 (s : real -> Prop) (l : real) : (has_inf s l) = (term10 s l).
Proof. exact (EQ_MP (@lem5305371 s l) (@lem5305370 s l)). Qed.
Lemma lem5305409 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305410 (s : real -> Prop) (l : real) : (term11 s l) = (term12 s l).
Proof. exact (MK_COMB (@lem5305409) (@lem5305390 s l)). Qed.
Lemma lem5305411 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5305412 (s : real -> Prop) (l : real) (c : real) : (term13 s l c) = (term14 s l c).
Proof. exact (MK_COMB (@lem5305410 s l) (@lem5305411 l c)). Qed.
Lemma lem5305415 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305416 (s : real -> Prop) (l : real) (c : real) : (term15 s l c) = (term16 s l c).
Proof. exact (MK_COMB (@lem5305415) (@lem5305412 s l c)). Qed.
Lemma lem5305423 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5305424 (l : real) (s : real -> Prop) (c : real) : (term18 l s c) = (term19 l s c).
Proof. exact (MK_COMB (@lem5305416 s l c) (@lem5305423 s c)). Qed.
Lemma lem5305427 (l : real) (s : real -> Prop) : (term20 l s) = (term21 l s).
Proof. exact (fun_ext (fun c : real => @lem5305424 l s c)). Qed.
Lemma lem5305428 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305429 (l : real) (s : real -> Prop) : (term22 l s) = (term23 l s).
Proof. exact (MK_COMB (@lem5305428) (@lem5305427 l s)). Qed.
Lemma lem5305434 (s : real -> Prop) : (term24 s) = (term25 s).
Proof. exact (fun_ext (fun l : real => @lem5305429 l s)). Qed.
Lemma lem5305435 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305436 (s : real -> Prop) : (term26 s) = (term27 s).
Proof. exact (MK_COMB (@lem5305435) (@lem5305434 s)). Qed.
Lemma lem5305441 : term28 = term29.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5305436 s)). Qed.
Lemma lem5305442 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5305443 : term30 = term31.
Proof. exact (MK_COMB (@lem5305442) (@lem5305441)). Qed.
Lemma lem5305448 : term31 = term30.
Proof. exact (SYM (@lem5305443)). Qed.
Lemma lem5305450 (p : Prop) : p = (term32 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5305451 : term31 = term33.
Proof. exact (@lem5305450 term31). Qed.
Lemma lem5305452 : term33 = term31.
Proof. exact (SYM (@lem5305451)). Qed.
Lemma lem5305453 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem5305456 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5305457 : term36.
Proof. exact (fun h0 : term35 => @lem5305456 h0). Qed.
Lemma lem5305458 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem5305459 (h1 : term35) : term35.
Proof. exact (h1). Qed.
Lemma lem5305460 (h1 : term35) (h2 : term36) : term35.
Proof. exact (@lem5305458 h2 (@lem5305459 h1)). Qed.
Lemma lem5305461 (h1 : term35) : term37.
Proof. exact (fun h0 : term36 => @lem5305460 h1 h0). Qed.
Lemma lem5305462 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem5305463 (h1 : term35) (h2 : term36) : term35.
Proof. exact (@lem5305461 h1 (@lem5305462 h2)). Qed.
Lemma lem5305464 (h1 : term36) : term36.
Proof. exact (fun h0 : term35 => @lem5305463 h0 h1). Qed.
Lemma lem5305465 : term38.
Proof. exact (fun h0 : term36 => @lem5305464 h0). Qed.
Lemma lem5305468 : term36.
Proof. exact (@lem5305465 (@lem5305457)). Qed.
Lemma lem5305552 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5305553 : term39 = term40.
Proof. exact (@lem5305552 term41). Qed.
Lemma lem5305628 : term42 = term42.
Proof. exact (eq_refl term42). Qed.
Lemma lem5305635 : term35 = term43.
Proof. exact (MK_COMB (@lem5305628) (@lem5305553)). Qed.
Lemma lem5305640 (s : real -> Prop) (x : real) (c : real) : (term44 s x c) = (term44 s x c).
Proof. exact (eq_refl (term44 s x c)). Qed.
Lemma lem5305641 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5305640 s x c)). Qed.
Lemma lem5305642 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305643 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5305642) (@lem5305641 s c)). Qed.
Lemma lem5305644 (s : real -> Prop) (c : real) : (term46 s c) = (term46 s c).
Proof. exact (eq_refl (term46 s c)). Qed.
Lemma lem5305649 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term47 s b x).
Proof. exact (eq_refl (term47 s b x)). Qed.
Lemma lem5305650 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5305649 s b x)). Qed.
Lemma lem5305651 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305652 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5305651) (@lem5305650 s b)). Qed.
Lemma lem5305653 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (fun_ext (fun b : real => @lem5305652 s b)). Qed.
Lemma lem5305654 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305655 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (MK_COMB (@lem5305654) (@lem5305653 s)). Qed.
Lemma lem5305656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305657 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem5305656) (@lem5305655 s)). Qed.
Lemma lem5305658 (s : real -> Prop) (c : real) : (term53 s c) = (term53 s c).
Proof. exact (MK_COMB (@lem5305657 s) (@lem5305644 s c)). Qed.
Lemma lem5305663 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5305664 (s : real -> Prop) (c : real) : (term55 s c) = (term55 s c).
Proof. exact (MK_COMB (@lem5305663 s) (@lem5305658 s c)). Qed.
Lemma lem5305665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305666 (s : real -> Prop) (c : real) : (term56 s c) = (term56 s c).
Proof. exact (MK_COMB (@lem5305665) (@lem5305664 s c)). Qed.
Lemma lem5305667 (s : real -> Prop) (c : real) : (term57 s c) = (term57 s c).
Proof. exact (MK_COMB (@lem5305666 s c) (@lem5305643 s c)). Qed.
Lemma lem5305668 (s : real -> Prop) : (term58 s) = (term58 s).
Proof. exact (fun_ext (fun c : real => @lem5305667 s c)). Qed.
Lemma lem5305669 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305670 (s : real -> Prop) : (term59 s) = (term59 s).
Proof. exact (MK_COMB (@lem5305669) (@lem5305668 s)). Qed.
Lemma lem5305671 : term60 = term60.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5305670 s)). Qed.
Lemma lem5305672 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5305673 : term41 = term41.
Proof. exact (MK_COMB (@lem5305672) (@lem5305671)). Qed.
Lemma lem5305674 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5305675 : term40 = term40.
Proof. exact (MK_COMB (@lem5305674) (@lem5305673)). Qed.
Lemma lem5305680 (s : real -> Prop) (x : real) (c : real) : (term44 s x c) = (term44 s x c).
Proof. exact (eq_refl (term44 s x c)). Qed.
Lemma lem5305681 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5305680 s x c)). Qed.
Lemma lem5305682 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305683 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5305682) (@lem5305681 s c)). Qed.
Lemma lem5305684 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5305685 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5305690 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term47 s b x).
Proof. exact (eq_refl (term47 s b x)). Qed.
Lemma lem5305691 (s : real -> Prop) (b : real) : (term48 s b) = (term48 s b).
Proof. exact (fun_ext (fun x : real => @lem5305690 s b x)). Qed.
Lemma lem5305692 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305693 (s : real -> Prop) (b : real) : (term49 s b) = (term49 s b).
Proof. exact (MK_COMB (@lem5305692) (@lem5305691 s b)). Qed.
Lemma lem5305694 (s : real -> Prop) : (term50 s) = (term50 s).
Proof. exact (fun_ext (fun b : real => @lem5305693 s b)). Qed.
Lemma lem5305695 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305696 (s : real -> Prop) : (term51 s) = (term51 s).
Proof. exact (MK_COMB (@lem5305695) (@lem5305694 s)). Qed.
Lemma lem5305697 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305698 (s : real -> Prop) : (term52 s) = (term52 s).
Proof. exact (MK_COMB (@lem5305697) (@lem5305696 s)). Qed.
Lemma lem5305699 (s : real -> Prop) (l : real) : (term61 s l) = (term61 s l).
Proof. exact (MK_COMB (@lem5305698 s) (@lem5305685 s l)). Qed.
Lemma lem5305704 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5305705 (s : real -> Prop) (l : real) : (term10 s l) = (term10 s l).
Proof. exact (MK_COMB (@lem5305704 s) (@lem5305699 s l)). Qed.
Lemma lem5305706 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305707 (s : real -> Prop) (l : real) : (term12 s l) = (term12 s l).
Proof. exact (MK_COMB (@lem5305706) (@lem5305705 s l)). Qed.
Lemma lem5305708 (s : real -> Prop) (l : real) (c : real) : (term14 s l c) = (term14 s l c).
Proof. exact (MK_COMB (@lem5305707 s l) (@lem5305684 l c)). Qed.
Lemma lem5305709 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305710 (s : real -> Prop) (l : real) (c : real) : (term16 s l c) = (term16 s l c).
Proof. exact (MK_COMB (@lem5305709) (@lem5305708 s l c)). Qed.
Lemma lem5305711 (l : real) (s : real -> Prop) (c : real) : (term19 l s c) = (term19 l s c).
Proof. exact (MK_COMB (@lem5305710 s l c) (@lem5305683 s c)). Qed.
Lemma lem5305712 (l : real) (s : real -> Prop) : (term21 l s) = (term21 l s).
Proof. exact (fun_ext (fun c : real => @lem5305711 l s c)). Qed.
Lemma lem5305713 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305714 (l : real) (s : real -> Prop) : (term23 l s) = (term23 l s).
Proof. exact (MK_COMB (@lem5305713) (@lem5305712 l s)). Qed.
Lemma lem5305715 (s : real -> Prop) : (term25 s) = (term25 s).
Proof. exact (fun_ext (fun l : real => @lem5305714 l s)). Qed.
Lemma lem5305716 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305717 (s : real -> Prop) : (term27 s) = (term27 s).
Proof. exact (MK_COMB (@lem5305716) (@lem5305715 s)). Qed.
Lemma lem5305718 : term29 = term29.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5305717 s)). Qed.
Lemma lem5305719 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5305720 : term31 = term31.
Proof. exact (MK_COMB (@lem5305719) (@lem5305718)). Qed.
Lemma lem5305721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5305722 : term34 = term34.
Proof. exact (MK_COMB (@lem5305721) (@lem5305720)). Qed.
Lemma lem5305723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5305724 : term42 = term42.
Proof. exact (MK_COMB (@lem5305723) (@lem5305722)). Qed.
Lemma lem5305725 : term43 = term43.
Proof. exact (MK_COMB (@lem5305724) (@lem5305675)). Qed.
Lemma lem5305818 : term35 = term43.
Proof. exact (TRANS (@lem5305635) (@lem5305725)). Qed.
Lemma lem5305819 : term43 = term35.
Proof. exact (SYM (@lem5305818)). Qed.
Lemma lem5305820 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem5305821 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem5305829 (s : real -> Prop) (b : real) (x : real) : (term47 s b x) = (term62 s b x).
Proof. exact (@lem17265 (@IN real x s) (real_le b x)). Qed.
Lemma lem5305830 (s : real -> Prop) (b : real) : (term48 s b) = (term63 s b).
Proof. exact (fun_ext (fun x : real => @lem5305829 s b x)). Qed.
Lemma lem5305831 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305832 (s : real -> Prop) (b : real) : (term49 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5305831) (@lem5305830 s b)). Qed.
Lemma lem5305833 (s : real -> Prop) : (term50 s) = (term65 s).
Proof. exact (fun_ext (fun b : real => @lem5305832 s b)). Qed.
Lemma lem5305834 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305835 (s : real -> Prop) : (term51 s) = (term66 s).
Proof. exact (MK_COMB (@lem5305834) (@lem5305833 s)). Qed.
Lemma lem5305836 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5305837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305838 (s : real -> Prop) : (term52 s) = (term67 s).
Proof. exact (MK_COMB (@lem5305837) (@lem5305835 s)). Qed.
Lemma lem5305839 (s : real -> Prop) (l : real) : (term61 s l) = (term68 s l).
Proof. exact (MK_COMB (@lem5305838 s) (@lem5305836 s l)). Qed.
Lemma lem5305841 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5305842 (s : real -> Prop) (l : real) : (term10 s l) = (term69 s l).
Proof. exact (MK_COMB (@lem5305841 s) (@lem5305839 s l)). Qed.
Lemma lem5305843 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5305844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305845 (s : real -> Prop) (l : real) : (term12 s l) = (term70 s l).
Proof. exact (MK_COMB (@lem5305844) (@lem5305842 s l)). Qed.
Lemma lem5305846 (s : real -> Prop) (l : real) (c : real) : (term14 s l c) = (term71 s l c).
Proof. exact (MK_COMB (@lem5305845 s l) (@lem5305843 l c)). Qed.
Lemma lem5305853 (s : real -> Prop) (x : real) (c : real) : (term72 s x c) = (term73 s x c).
Proof. exact (@lem17045 (@IN real x s) (real_lt x c)). Qed.
Lemma lem5305854 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5305855 (s : real -> Prop) (c : real) : (term76 s c) = (term77 s c).
Proof. exact (@lem5305854 (term45 s c)). Qed.
Lemma lem5305856 (s : real -> Prop) (x : real) (c : real) : (term78 s c x) = (term44 s x c).
Proof. exact (eq_refl (term78 s c x)). Qed.
Lemma lem5305857 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5305858 (s : real -> Prop) (x : real) (c : real) : (term79 s c x) = (term72 s x c).
Proof. exact (MK_COMB (@lem5305857) (@lem5305856 s x c)). Qed.
Lemma lem5305859 (s : real -> Prop) (x : real) (c : real) : (term79 s c x) = (term73 s x c).
Proof. exact (TRANS (@lem5305858 s x c) (@lem5305853 s x c)). Qed.
Lemma lem5305860 (s : real -> Prop) (c : real) : (term80 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5305859 s x c)). Qed.
Lemma lem5305861 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5305862 (s : real -> Prop) (c : real) : (term77 s c) = (term82 s c).
Proof. exact (MK_COMB (@lem5305861) (@lem5305860 s c)). Qed.
Lemma lem5305863 (s : real -> Prop) (c : real) : (term76 s c) = (term82 s c).
Proof. exact (TRANS (@lem5305855 s c) (@lem5305862 s c)). Qed.
Lemma lem5305864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5305865 (s : real -> Prop) (l : real) (c : real) : (term83 s l c) = (term84 s l c).
Proof. exact (MK_COMB (@lem5305864) (@lem5305846 s l c)). Qed.
Lemma lem5305866 (l : real) (s : real -> Prop) (c : real) : (term85 l s c) = (term86 l s c).
Proof. exact (MK_COMB (@lem5305865 s l c) (@lem5305863 s c)). Qed.
Lemma lem5305867 (l : real) (s : real -> Prop) (c : real) : (term87 l s c) = (term85 l s c).
Proof. exact (@lem17362 (term14 s l c) (term17 s c)). Qed.
Lemma lem5305868 (l : real) (s : real -> Prop) (c : real) : (term87 l s c) = (term86 l s c).
Proof. exact (TRANS (@lem5305867 l s c) (@lem5305866 l s c)). Qed.
Lemma lem5305869 (P : real -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5305870 (l : real) (s : real -> Prop) : (term90 l s) = (term91 l s).
Proof. exact (@lem5305869 (term21 l s)). Qed.
Lemma lem5305871 (l : real) (s : real -> Prop) (c : real) : (term92 l s c) = (term19 l s c).
Proof. exact (eq_refl (term92 l s c)). Qed.
Lemma lem5305872 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5305873 (l : real) (s : real -> Prop) (c : real) : (term93 l s c) = (term87 l s c).
Proof. exact (MK_COMB (@lem5305872) (@lem5305871 l s c)). Qed.
Lemma lem5305874 (l : real) (s : real -> Prop) (c : real) : (term93 l s c) = (term86 l s c).
Proof. exact (TRANS (@lem5305873 l s c) (@lem5305868 l s c)). Qed.
Lemma lem5305875 (l : real) (s : real -> Prop) : (term94 l s) = (term95 l s).
Proof. exact (fun_ext (fun c : real => @lem5305874 l s c)). Qed.
Lemma lem5305876 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305877 (l : real) (s : real -> Prop) : (term91 l s) = (term96 l s).
Proof. exact (MK_COMB (@lem5305876) (@lem5305875 l s)). Qed.
Lemma lem5305878 (l : real) (s : real -> Prop) : (term90 l s) = (term96 l s).
Proof. exact (TRANS (@lem5305870 l s) (@lem5305877 l s)). Qed.
Lemma lem5305879 (P : real -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5305880 (s : real -> Prop) : (term97 s) = (term98 s).
Proof. exact (@lem5305879 (term25 s)). Qed.
Lemma lem5305881 (l : real) (s : real -> Prop) : (term99 s l) = (term23 l s).
Proof. exact (eq_refl (term99 s l)). Qed.
Lemma lem5305882 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5305883 (l : real) (s : real -> Prop) : (term100 s l) = (term90 l s).
Proof. exact (MK_COMB (@lem5305882) (@lem5305881 l s)). Qed.
Lemma lem5305884 (l : real) (s : real -> Prop) : (term100 s l) = (term96 l s).
Proof. exact (TRANS (@lem5305883 l s) (@lem5305878 l s)). Qed.
Lemma lem5305885 (s : real -> Prop) : (term101 s) = (term102 s).
Proof. exact (fun_ext (fun l : real => @lem5305884 l s)). Qed.
Lemma lem5305886 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5305887 (s : real -> Prop) : (term98 s) = (term103 s).
Proof. exact (MK_COMB (@lem5305886) (@lem5305885 s)). Qed.
Lemma lem5305888 (s : real -> Prop) : (term97 s) = (term103 s).
Proof. exact (TRANS (@lem5305880 s) (@lem5305887 s)). Qed.
Lemma lem5305889 (P : type1022) : (term104 P) = (term105 P).
Proof. exact (@lem18392 (real -> Prop) P). Qed.
Lemma lem5305890 : term34 = term106.
Proof. exact (@lem5305889 term29). Qed.
Lemma lem5305891 (s : real -> Prop) : (term107 s) = (term27 s).
Proof. exact (eq_refl (term107 s)). Qed.
Lemma lem5305892 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5305893 (s : real -> Prop) : (term108 s) = (term97 s).
Proof. exact (MK_COMB (@lem5305892) (@lem5305891 s)). Qed.
Lemma lem5305894 (s : real -> Prop) : (term108 s) = (term103 s).
Proof. exact (TRANS (@lem5305893 s) (@lem5305888 s)). Qed.
Lemma lem5305895 : term109 = term110.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5305894 s)). Qed.
Lemma lem5305896 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5305897 : term106 = term111.
Proof. exact (MK_COMB (@lem5305896) (@lem5305895)). Qed.
Lemma lem5305898 : term34 = term111.
Proof. exact (TRANS (@lem5305890) (@lem5305897)). Qed.
Lemma lem5306057 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5306058 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5306057 real P Q). Qed.
Lemma lem5306059 (s : real -> Prop) (l : real) : (term116 s l) = (term117 s l).
Proof. exact (@lem5306058 (term65 s) ((inf s) = l)). Qed.
Lemma lem5306060 (s : real -> Prop) (b : real) : (term118 s b) = (term64 s b).
Proof. exact (eq_refl (term118 s b)). Qed.
Lemma lem5306061 (s : real -> Prop) : (term119 s) = (term65 s).
Proof. exact (fun_ext (fun b : real => @lem5306060 s b)). Qed.
Lemma lem5306062 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306063 (s : real -> Prop) : (term120 s) = (term66 s).
Proof. exact (MK_COMB (@lem5306062) (@lem5306061 s)). Qed.
Lemma lem5306064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306065 (s : real -> Prop) : (term121 s) = (term67 s).
Proof. exact (MK_COMB (@lem5306064) (@lem5306063 s)). Qed.
Lemma lem5306066 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5306067 (s : real -> Prop) (l : real) : (term116 s l) = (term68 s l).
Proof. exact (MK_COMB (@lem5306065 s) (@lem5306066 s l)). Qed.
Lemma lem5306068 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306069 (s : real -> Prop) (l : real) : (term122 s l) = (term123 s l).
Proof. exact (MK_COMB (@lem5306068) (@lem5306067 s l)). Qed.
Lemma lem5306070 (s : real -> Prop) (b : real) : (term118 s b) = (term64 s b).
Proof. exact (eq_refl (term118 s b)). Qed.
Lemma lem5306071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306072 (s : real -> Prop) (b : real) : (term124 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5306071) (@lem5306070 s b)). Qed.
Lemma lem5306073 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5306074 (b : real) (s : real -> Prop) (l : real) : (term126 b s l) = (term127 b s l).
Proof. exact (MK_COMB (@lem5306072 s b) (@lem5306073 s l)). Qed.
Lemma lem5306075 (s : real -> Prop) (l : real) : (term128 s l) = (term129 s l).
Proof. exact (fun_ext (fun b : real => @lem5306074 b s l)). Qed.
Lemma lem5306076 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306077 (s : real -> Prop) (l : real) : (term117 s l) = (term130 s l).
Proof. exact (MK_COMB (@lem5306076) (@lem5306075 s l)). Qed.
Lemma lem5306078 (s : real -> Prop) (l : real) : ((term116 s l) = (term117 s l)) = ((term68 s l) = (term130 s l)).
Proof. exact (MK_COMB (@lem5306069 s l) (@lem5306077 s l)). Qed.
Lemma lem5306079 (s : real -> Prop) (l : real) : (term68 s l) = (term130 s l).
Proof. exact (EQ_MP (@lem5306078 s l) (@lem5306059 s l)). Qed.
Lemma lem5306080 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5306081 (s : real -> Prop) (l : real) : (term69 s l) = (term131 s l).
Proof. exact (MK_COMB (@lem5306080 s) (@lem5306079 s l)). Qed.
Lemma lem5306083 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term133 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem5306084 (P : Prop) (Q : real -> Prop) : (term134 P Q) = (term135 P Q).
Proof. exact (@lem5306083 real P Q). Qed.
Lemma lem5306085 (s : real -> Prop) (l : real) : (term136 s l) = (term137 s l).
Proof. exact (@lem5306084 (term138 s) (term129 s l)). Qed.
Lemma lem5306086 (b : real) (s : real -> Prop) (l : real) : (term139 s l b) = (term127 b s l).
Proof. exact (eq_refl (term139 s l b)). Qed.
Lemma lem5306087 (s : real -> Prop) (l : real) : (term140 s l) = (term129 s l).
Proof. exact (fun_ext (fun b : real => @lem5306086 b s l)). Qed.
Lemma lem5306088 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306089 (s : real -> Prop) (l : real) : (term141 s l) = (term130 s l).
Proof. exact (MK_COMB (@lem5306088) (@lem5306087 s l)). Qed.
Lemma lem5306090 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5306091 (s : real -> Prop) (l : real) : (term136 s l) = (term131 s l).
Proof. exact (MK_COMB (@lem5306090 s) (@lem5306089 s l)). Qed.
Lemma lem5306092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306093 (s : real -> Prop) (l : real) : (term142 s l) = (term143 s l).
Proof. exact (MK_COMB (@lem5306092) (@lem5306091 s l)). Qed.
Lemma lem5306094 (b : real) (s : real -> Prop) (l : real) : (term139 s l b) = (term127 b s l).
Proof. exact (eq_refl (term139 s l b)). Qed.
Lemma lem5306095 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5306096 (b : real) (s : real -> Prop) (l : real) : (term144 s l b) = (term145 b s l).
Proof. exact (MK_COMB (@lem5306095 s) (@lem5306094 b s l)). Qed.
Lemma lem5306097 (s : real -> Prop) (l : real) : (term146 s l) = (term147 s l).
Proof. exact (fun_ext (fun b : real => @lem5306096 b s l)). Qed.
Lemma lem5306098 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306099 (s : real -> Prop) (l : real) : (term137 s l) = (term148 s l).
Proof. exact (MK_COMB (@lem5306098) (@lem5306097 s l)). Qed.
Lemma lem5306100 (s : real -> Prop) (l : real) : ((term136 s l) = (term137 s l)) = ((term131 s l) = (term148 s l)).
Proof. exact (MK_COMB (@lem5306093 s l) (@lem5306099 s l)). Qed.
Lemma lem5306101 (s : real -> Prop) (l : real) : (term131 s l) = (term148 s l).
Proof. exact (EQ_MP (@lem5306100 s l) (@lem5306085 s l)). Qed.
Lemma lem5306102 (s : real -> Prop) (l : real) : (term69 s l) = (term148 s l).
Proof. exact (TRANS (@lem5306081 s l) (@lem5306101 s l)). Qed.
Lemma lem5306103 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306104 (s : real -> Prop) (l : real) : (term70 s l) = (term149 s l).
Proof. exact (MK_COMB (@lem5306103) (@lem5306102 s l)). Qed.
Lemma lem5306105 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5306106 (s : real -> Prop) (l : real) (c : real) : (term71 s l c) = (term150 s l c).
Proof. exact (MK_COMB (@lem5306104 s l) (@lem5306105 l c)). Qed.
Lemma lem5306108 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5306109 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5306108 real P Q). Qed.
Lemma lem5306110 (s : real -> Prop) (l : real) (c : real) : (term151 s l c) = (term152 s l c).
Proof. exact (@lem5306109 (term147 s l) (real_lt l c)). Qed.
Lemma lem5306111 (b : real) (s : real -> Prop) (l : real) : (term153 s l b) = (term145 b s l).
Proof. exact (eq_refl (term153 s l b)). Qed.
Lemma lem5306112 (s : real -> Prop) (l : real) : (term154 s l) = (term147 s l).
Proof. exact (fun_ext (fun b : real => @lem5306111 b s l)). Qed.
Lemma lem5306113 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306114 (s : real -> Prop) (l : real) : (term155 s l) = (term148 s l).
Proof. exact (MK_COMB (@lem5306113) (@lem5306112 s l)). Qed.
Lemma lem5306115 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306116 (s : real -> Prop) (l : real) : (term156 s l) = (term149 s l).
Proof. exact (MK_COMB (@lem5306115) (@lem5306114 s l)). Qed.
Lemma lem5306117 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5306118 (s : real -> Prop) (l : real) (c : real) : (term151 s l c) = (term150 s l c).
Proof. exact (MK_COMB (@lem5306116 s l) (@lem5306117 l c)). Qed.
Lemma lem5306119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306120 (s : real -> Prop) (l : real) (c : real) : (term157 s l c) = (term158 s l c).
Proof. exact (MK_COMB (@lem5306119) (@lem5306118 s l c)). Qed.
Lemma lem5306121 (b : real) (s : real -> Prop) (l : real) : (term153 s l b) = (term145 b s l).
Proof. exact (eq_refl (term153 s l b)). Qed.
Lemma lem5306122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306123 (b : real) (s : real -> Prop) (l : real) : (term159 s l b) = (term160 b s l).
Proof. exact (MK_COMB (@lem5306122) (@lem5306121 b s l)). Qed.
Lemma lem5306124 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5306125 (b : real) (s : real -> Prop) (l : real) (c : real) : (term161 s b l c) = (term162 b s l c).
Proof. exact (MK_COMB (@lem5306123 b s l) (@lem5306124 l c)). Qed.
Lemma lem5306126 (s : real -> Prop) (l : real) (c : real) : (term163 s l c) = (term164 s l c).
Proof. exact (fun_ext (fun b : real => @lem5306125 b s l c)). Qed.
Lemma lem5306127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306128 (s : real -> Prop) (l : real) (c : real) : (term152 s l c) = (term165 s l c).
Proof. exact (MK_COMB (@lem5306127) (@lem5306126 s l c)). Qed.
Lemma lem5306129 (s : real -> Prop) (l : real) (c : real) : ((term151 s l c) = (term152 s l c)) = ((term150 s l c) = (term165 s l c)).
Proof. exact (MK_COMB (@lem5306120 s l c) (@lem5306128 s l c)). Qed.
Lemma lem5306130 (s : real -> Prop) (l : real) (c : real) : (term150 s l c) = (term165 s l c).
Proof. exact (EQ_MP (@lem5306129 s l c) (@lem5306110 s l c)). Qed.
Lemma lem5306131 (s : real -> Prop) (l : real) (c : real) : (term71 s l c) = (term165 s l c).
Proof. exact (TRANS (@lem5306106 s l c) (@lem5306130 s l c)). Qed.
Lemma lem5306132 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306133 (s : real -> Prop) (l : real) (c : real) : (term84 s l c) = (term166 s l c).
Proof. exact (MK_COMB (@lem5306132) (@lem5306131 s l c)). Qed.
Lemma lem5306134 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (eq_refl (term82 s c)). Qed.
Lemma lem5306135 (l : real) (s : real -> Prop) (c : real) : (term86 l s c) = (term167 l s c).
Proof. exact (MK_COMB (@lem5306133 s l c) (@lem5306134 s c)). Qed.
Lemma lem5306137 {A : Type'} (P : A -> Prop) (Q : Prop) : (term112 A P Q) = (term113 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem5306138 (P : real -> Prop) (Q : Prop) : (term114 P Q) = (term115 P Q).
Proof. exact (@lem5306137 real P Q). Qed.
Lemma lem5306139 (l : real) (s : real -> Prop) (c : real) : (term168 l s c) = (term169 l s c).
Proof. exact (@lem5306138 (term164 s l c) (term82 s c)). Qed.
Lemma lem5306140 (b : real) (s : real -> Prop) (l : real) (c : real) : (term170 s l c b) = (term162 b s l c).
Proof. exact (eq_refl (term170 s l c b)). Qed.
Lemma lem5306141 (s : real -> Prop) (l : real) (c : real) : (term171 s l c) = (term164 s l c).
Proof. exact (fun_ext (fun b : real => @lem5306140 b s l c)). Qed.
Lemma lem5306142 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306143 (s : real -> Prop) (l : real) (c : real) : (term172 s l c) = (term165 s l c).
Proof. exact (MK_COMB (@lem5306142) (@lem5306141 s l c)). Qed.
Lemma lem5306144 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306145 (s : real -> Prop) (l : real) (c : real) : (term173 s l c) = (term166 s l c).
Proof. exact (MK_COMB (@lem5306144) (@lem5306143 s l c)). Qed.
Lemma lem5306146 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (eq_refl (term82 s c)). Qed.
Lemma lem5306147 (l : real) (s : real -> Prop) (c : real) : (term168 l s c) = (term167 l s c).
Proof. exact (MK_COMB (@lem5306145 s l c) (@lem5306146 s c)). Qed.
Lemma lem5306148 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306149 (l : real) (s : real -> Prop) (c : real) : (term174 l s c) = (term175 l s c).
Proof. exact (MK_COMB (@lem5306148) (@lem5306147 l s c)). Qed.
Lemma lem5306150 (b : real) (s : real -> Prop) (l : real) (c : real) : (term170 s l c b) = (term162 b s l c).
Proof. exact (eq_refl (term170 s l c b)). Qed.
Lemma lem5306151 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306152 (b : real) (s : real -> Prop) (l : real) (c : real) : (term176 s l c b) = (term177 b s l c).
Proof. exact (MK_COMB (@lem5306151) (@lem5306150 b s l c)). Qed.
Lemma lem5306153 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (eq_refl (term82 s c)). Qed.
Lemma lem5306154 (b : real) (l : real) (s : real -> Prop) (c : real) : (term178 l b s c) = (term179 b l s c).
Proof. exact (MK_COMB (@lem5306152 b s l c) (@lem5306153 s c)). Qed.
Lemma lem5306155 (l : real) (s : real -> Prop) (c : real) : (term180 l s c) = (term181 l s c).
Proof. exact (fun_ext (fun b : real => @lem5306154 b l s c)). Qed.
Lemma lem5306156 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306157 (l : real) (s : real -> Prop) (c : real) : (term169 l s c) = (term182 l s c).
Proof. exact (MK_COMB (@lem5306156) (@lem5306155 l s c)). Qed.
Lemma lem5306158 (l : real) (s : real -> Prop) (c : real) : ((term168 l s c) = (term169 l s c)) = ((term167 l s c) = (term182 l s c)).
Proof. exact (MK_COMB (@lem5306149 l s c) (@lem5306157 l s c)). Qed.
Lemma lem5306159 (l : real) (s : real -> Prop) (c : real) : (term167 l s c) = (term182 l s c).
Proof. exact (EQ_MP (@lem5306158 l s c) (@lem5306139 l s c)). Qed.
Lemma lem5306160 (l : real) (s : real -> Prop) (c : real) : (term86 l s c) = (term182 l s c).
Proof. exact (TRANS (@lem5306135 l s c) (@lem5306159 l s c)). Qed.
Lemma lem5306161 (l : real) (s : real -> Prop) : (term95 l s) = (term183 l s).
Proof. exact (fun_ext (fun c : real => @lem5306160 l s c)). Qed.
Lemma lem5306162 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306163 (l : real) (s : real -> Prop) : (term96 l s) = (term184 l s).
Proof. exact (MK_COMB (@lem5306162) (@lem5306161 l s)). Qed.
Lemma lem5306164 (s : real -> Prop) : (term102 s) = (term185 s).
Proof. exact (fun_ext (fun l : real => @lem5306163 l s)). Qed.
Lemma lem5306165 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306166 (s : real -> Prop) : (term103 s) = (term186 s).
Proof. exact (MK_COMB (@lem5306165) (@lem5306164 s)). Qed.
Lemma lem5306167 : term110 = term187.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306166 s)). Qed.
Lemma lem5306168 : (@ex (real -> Prop)) = (@ex (real -> Prop)).
Proof. exact (eq_refl (@ex (real -> Prop))). Qed.
Lemma lem5306170 : term111 = term188.
Proof. exact (MK_COMB (@lem5306168) (@lem5306167)). Qed.
Lemma lem5306171 : term34 = term188.
Proof. exact (TRANS (@lem5305898) (@lem5306170)). Qed.
Lemma lem5306172 (h1 : term34) : term188.
Proof. exact (EQ_MP (@lem5306171) (@lem5305820 h1)). Qed.
Lemma lem5306175 (s : real -> Prop) : (term189 s) = (s = (@EMPTY real)).
Proof. exact (@lem16933 (s = (@EMPTY real))). Qed.
Lemma lem5306182 (s : real -> Prop) (b : real) (x : real) : (term190 s b x) = (term191 s b x).
Proof. exact (@lem17362 (@IN real x s) (real_le b x)). Qed.
Lemma lem5306183 (P : real -> Prop) : (term88 P) = (term89 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem5306184 (s : real -> Prop) (b : real) : (term192 s b) = (term193 s b).
Proof. exact (@lem5306183 (term48 s b)). Qed.
Lemma lem5306185 (s : real -> Prop) (b : real) (x : real) : (term194 s b x) = (term47 s b x).
Proof. exact (eq_refl (term194 s b x)). Qed.
Lemma lem5306186 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5306187 (s : real -> Prop) (b : real) (x : real) : (term195 s b x) = (term190 s b x).
Proof. exact (MK_COMB (@lem5306186) (@lem5306185 s b x)). Qed.
Lemma lem5306188 (s : real -> Prop) (b : real) (x : real) : (term195 s b x) = (term191 s b x).
Proof. exact (TRANS (@lem5306187 s b x) (@lem5306182 s b x)). Qed.
Lemma lem5306189 (s : real -> Prop) (b : real) : (term196 s b) = (term197 s b).
Proof. exact (fun_ext (fun x : real => @lem5306188 s b x)). Qed.
Lemma lem5306190 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306191 (s : real -> Prop) (b : real) : (term193 s b) = (term198 s b).
Proof. exact (MK_COMB (@lem5306190) (@lem5306189 s b)). Qed.
Lemma lem5306192 (s : real -> Prop) (b : real) : (term192 s b) = (term198 s b).
Proof. exact (TRANS (@lem5306184 s b) (@lem5306191 s b)). Qed.
Lemma lem5306193 (P : real -> Prop) : (term74 P) = (term75 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem5306194 (s : real -> Prop) : (term199 s) = (term200 s).
Proof. exact (@lem5306193 (term50 s)). Qed.
Lemma lem5306195 (s : real -> Prop) (b : real) : (term201 s b) = (term49 s b).
Proof. exact (eq_refl (term201 s b)). Qed.
Lemma lem5306196 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5306197 (s : real -> Prop) (b : real) : (term202 s b) = (term192 s b).
Proof. exact (MK_COMB (@lem5306196) (@lem5306195 s b)). Qed.
Lemma lem5306198 (s : real -> Prop) (b : real) : (term202 s b) = (term198 s b).
Proof. exact (TRANS (@lem5306197 s b) (@lem5306192 s b)). Qed.
Lemma lem5306199 (s : real -> Prop) : (term203 s) = (term204 s).
Proof. exact (fun_ext (fun b : real => @lem5306198 s b)). Qed.
Lemma lem5306200 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306201 (s : real -> Prop) : (term200 s) = (term205 s).
Proof. exact (MK_COMB (@lem5306200) (@lem5306199 s)). Qed.
Lemma lem5306202 (s : real -> Prop) : (term199 s) = (term205 s).
Proof. exact (TRANS (@lem5306194 s) (@lem5306201 s)). Qed.
Lemma lem5306203 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306204 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306205 (s : real -> Prop) : (term207 s) = (term208 s).
Proof. exact (MK_COMB (@lem5306204) (@lem5306202 s)). Qed.
Lemma lem5306206 (s : real -> Prop) (c : real) : (term209 s c) = (term210 s c).
Proof. exact (MK_COMB (@lem5306205 s) (@lem5306203 s c)). Qed.
Lemma lem5306207 (s : real -> Prop) (c : real) : (term211 s c) = (term209 s c).
Proof. exact (@lem17045 (term51 s) (term46 s c)). Qed.
Lemma lem5306208 (s : real -> Prop) (c : real) : (term211 s c) = (term210 s c).
Proof. exact (TRANS (@lem5306207 s c) (@lem5306206 s c)). Qed.
Lemma lem5306209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306210 (s : real -> Prop) : (term212 s) = (term213 s).
Proof. exact (MK_COMB (@lem5306209) (@lem5306175 s)). Qed.
Lemma lem5306211 (s : real -> Prop) (c : real) : (term214 s c) = (term215 s c).
Proof. exact (MK_COMB (@lem5306210 s) (@lem5306208 s c)). Qed.
Lemma lem5306212 (s : real -> Prop) (c : real) : (term216 s c) = (term214 s c).
Proof. exact (@lem17045 (term138 s) (term53 s c)). Qed.
Lemma lem5306213 (s : real -> Prop) (c : real) : (term216 s c) = (term215 s c).
Proof. exact (TRANS (@lem5306212 s c) (@lem5306211 s c)). Qed.
Lemma lem5306218 (s : real -> Prop) (x : real) (c : real) : (term44 s x c) = (term44 s x c).
Proof. exact (eq_refl (term44 s x c)). Qed.
Lemma lem5306219 (s : real -> Prop) (c : real) : (term45 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5306218 s x c)). Qed.
Lemma lem5306220 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306221 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5306220) (@lem5306219 s c)). Qed.
Lemma lem5306222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306223 (s : real -> Prop) (c : real) : (term217 s c) = (term218 s c).
Proof. exact (MK_COMB (@lem5306222) (@lem5306213 s c)). Qed.
Lemma lem5306224 (s : real -> Prop) (c : real) : (term219 s c) = (term220 s c).
Proof. exact (MK_COMB (@lem5306223 s c) (@lem5306221 s c)). Qed.
Lemma lem5306225 (s : real -> Prop) (c : real) : (term57 s c) = (term219 s c).
Proof. exact (@lem17265 (term55 s c) (term17 s c)). Qed.
Lemma lem5306226 (s : real -> Prop) (c : real) : (term57 s c) = (term220 s c).
Proof. exact (TRANS (@lem5306225 s c) (@lem5306224 s c)). Qed.
Lemma lem5306227 (s : real -> Prop) : (term58 s) = (term221 s).
Proof. exact (fun_ext (fun c : real => @lem5306226 s c)). Qed.
Lemma lem5306228 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306229 (s : real -> Prop) : (term59 s) = (term222 s).
Proof. exact (MK_COMB (@lem5306228) (@lem5306227 s)). Qed.
Lemma lem5306230 : term60 = term223.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306229 s)). Qed.
Lemma lem5306231 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306232 : term41 = term224.
Proof. exact (MK_COMB (@lem5306231) (@lem5306230)). Qed.
Lemma lem5306387 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5306388 (P : type1626) : (term227 P) = (term228 P).
Proof. exact (@lem5306387 real real P). Qed.
Lemma lem5306389 (s : real -> Prop) : (term229 s) = (term230 s).
Proof. exact (@lem5306388 (term231 s)). Qed.
Lemma lem5306390 (s : real -> Prop) (b : real) : (term232 s b) = (term197 s b).
Proof. exact (eq_refl (term232 s b)). Qed.
Lemma lem5306391 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5306392 (s : real -> Prop) (b : real) (x : real) : (term233 s b x) = (term234 s b x).
Proof. exact (MK_COMB (@lem5306390 s b) (@lem5306391 x)). Qed.
Lemma lem5306393 (s : real -> Prop) (b : real) (x : real) : (term234 s b x) = (term191 s b x).
Proof. exact (eq_refl (term234 s b x)). Qed.
Lemma lem5306394 (s : real -> Prop) (b : real) (x : real) : (term233 s b x) = (term191 s b x).
Proof. exact (TRANS (@lem5306392 s b x) (@lem5306393 s b x)). Qed.
Lemma lem5306395 (s : real -> Prop) (b : real) : (term235 s b) = (term197 s b).
Proof. exact (fun_ext (fun x : real => @lem5306394 s b x)). Qed.
Lemma lem5306396 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306397 (s : real -> Prop) (b : real) : (term236 s b) = (term198 s b).
Proof. exact (MK_COMB (@lem5306396) (@lem5306395 s b)). Qed.
Lemma lem5306398 (s : real -> Prop) : (term237 s) = (term204 s).
Proof. exact (fun_ext (fun b : real => @lem5306397 s b)). Qed.
Lemma lem5306399 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306400 (s : real -> Prop) : (term229 s) = (term205 s).
Proof. exact (MK_COMB (@lem5306399) (@lem5306398 s)). Qed.
Lemma lem5306401 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306402 (s : real -> Prop) : (term238 s) = (term239 s).
Proof. exact (MK_COMB (@lem5306401) (@lem5306400 s)). Qed.
Lemma lem5306403 (s : real -> Prop) (b : real) : (term232 s b) = (term197 s b).
Proof. exact (eq_refl (term232 s b)). Qed.
Lemma lem5306404 (x : real -> real) (b : real) : (x b) = (x b).
Proof. exact (eq_refl (x b)). Qed.
Lemma lem5306405 (s : real -> Prop) (x : real -> real) (b : real) : (term240 s x b) = (term241 s x b).
Proof. exact (MK_COMB (@lem5306403 s b) (@lem5306404 x b)). Qed.
Lemma lem5306406 (s : real -> Prop) (x : real -> real) (b : real) : (term241 s x b) = (term242 s x b).
Proof. exact (eq_refl (term241 s x b)). Qed.
Lemma lem5306407 (s : real -> Prop) (x : real -> real) (b : real) : (term240 s x b) = (term242 s x b).
Proof. exact (TRANS (@lem5306405 s x b) (@lem5306406 s x b)). Qed.
Lemma lem5306408 (s : real -> Prop) (x : real -> real) : (term243 s x) = (term244 s x).
Proof. exact (fun_ext (fun b : real => @lem5306407 s x b)). Qed.
Lemma lem5306409 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306410 (s : real -> Prop) (x : real -> real) : (term245 s x) = (term246 s x).
Proof. exact (MK_COMB (@lem5306409) (@lem5306408 s x)). Qed.
Lemma lem5306411 (s : real -> Prop) : (term247 s) = (term248 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5306410 s x)). Qed.
Lemma lem5306412 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306413 (s : real -> Prop) : (term230 s) = (term249 s).
Proof. exact (MK_COMB (@lem5306412) (@lem5306411 s)). Qed.
Lemma lem5306414 (s : real -> Prop) : ((term229 s) = (term230 s)) = ((term205 s) = (term249 s)).
Proof. exact (MK_COMB (@lem5306402 s) (@lem5306413 s)). Qed.
Lemma lem5306415 (s : real -> Prop) : (term205 s) = (term249 s).
Proof. exact (EQ_MP (@lem5306414 s) (@lem5306389 s)). Qed.
Lemma lem5306416 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306417 (s : real -> Prop) : (term208 s) = (term250 s).
Proof. exact (MK_COMB (@lem5306416) (@lem5306415 s)). Qed.
Lemma lem5306418 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306419 (s : real -> Prop) (c : real) : (term210 s c) = (term251 s c).
Proof. exact (MK_COMB (@lem5306417 s) (@lem5306418 s c)). Qed.
Lemma lem5306421 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5306422 (P : type1028) (Q : Prop) : (term254 P Q) = (term255 P Q).
Proof. exact (@lem5306421 (real -> real) P Q). Qed.
Lemma lem5306423 (s : real -> Prop) (c : real) : (term256 s c) = (term257 s c).
Proof. exact (@lem5306422 (term248 s) (term206 s c)). Qed.
Lemma lem5306424 (s : real -> Prop) (x : real -> real) : (term258 s x) = (term246 s x).
Proof. exact (eq_refl (term258 s x)). Qed.
Lemma lem5306425 (s : real -> Prop) : (term259 s) = (term248 s).
Proof. exact (fun_ext (fun x : real -> real => @lem5306424 s x)). Qed.
Lemma lem5306426 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306427 (s : real -> Prop) : (term260 s) = (term249 s).
Proof. exact (MK_COMB (@lem5306426) (@lem5306425 s)). Qed.
Lemma lem5306428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306429 (s : real -> Prop) : (term261 s) = (term250 s).
Proof. exact (MK_COMB (@lem5306428) (@lem5306427 s)). Qed.
Lemma lem5306430 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306431 (s : real -> Prop) (c : real) : (term256 s c) = (term251 s c).
Proof. exact (MK_COMB (@lem5306429 s) (@lem5306430 s c)). Qed.
Lemma lem5306432 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306433 (s : real -> Prop) (c : real) : (term262 s c) = (term263 s c).
Proof. exact (MK_COMB (@lem5306432) (@lem5306431 s c)). Qed.
Lemma lem5306434 (s : real -> Prop) (x : real -> real) : (term258 s x) = (term246 s x).
Proof. exact (eq_refl (term258 s x)). Qed.
Lemma lem5306435 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306436 (s : real -> Prop) (x : real -> real) : (term264 s x) = (term265 s x).
Proof. exact (MK_COMB (@lem5306435) (@lem5306434 s x)). Qed.
Lemma lem5306437 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306438 (x : real -> real) (s : real -> Prop) (c : real) : (term266 x s c) = (term267 x s c).
Proof. exact (MK_COMB (@lem5306436 s x) (@lem5306437 s c)). Qed.
Lemma lem5306439 (s : real -> Prop) (c : real) : (term268 s c) = (term269 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306438 x s c)). Qed.
Lemma lem5306440 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306441 (s : real -> Prop) (c : real) : (term257 s c) = (term270 s c).
Proof. exact (MK_COMB (@lem5306440) (@lem5306439 s c)). Qed.
Lemma lem5306442 (s : real -> Prop) (c : real) : ((term256 s c) = (term257 s c)) = ((term251 s c) = (term270 s c)).
Proof. exact (MK_COMB (@lem5306433 s c) (@lem5306441 s c)). Qed.
Lemma lem5306443 (s : real -> Prop) (c : real) : (term251 s c) = (term270 s c).
Proof. exact (EQ_MP (@lem5306442 s c) (@lem5306423 s c)). Qed.
Lemma lem5306444 (s : real -> Prop) (c : real) : (term210 s c) = (term270 s c).
Proof. exact (TRANS (@lem5306419 s c) (@lem5306443 s c)). Qed.
Lemma lem5306445 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306446 (s : real -> Prop) (c : real) : (term215 s c) = (term271 s c).
Proof. exact (MK_COMB (@lem5306445 s) (@lem5306444 s c)). Qed.
Lemma lem5306448 {A : Type'} (P : Prop) (Q : A -> Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5306449 (P : Prop) (Q : type1028) : (term274 P Q) = (term275 P Q).
Proof. exact (@lem5306448 (real -> real) P Q). Qed.
Lemma lem5306450 (s : real -> Prop) (c : real) : (term276 s c) = (term277 s c).
Proof. exact (@lem5306449 (s = (@EMPTY real)) (term269 s c)). Qed.
Lemma lem5306451 (x : real -> real) (s : real -> Prop) (c : real) : (term278 s c x) = (term267 x s c).
Proof. exact (eq_refl (term278 s c x)). Qed.
Lemma lem5306452 (s : real -> Prop) (c : real) : (term279 s c) = (term269 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306451 x s c)). Qed.
Lemma lem5306453 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306454 (s : real -> Prop) (c : real) : (term280 s c) = (term270 s c).
Proof. exact (MK_COMB (@lem5306453) (@lem5306452 s c)). Qed.
Lemma lem5306455 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306456 (s : real -> Prop) (c : real) : (term276 s c) = (term271 s c).
Proof. exact (MK_COMB (@lem5306455 s) (@lem5306454 s c)). Qed.
Lemma lem5306457 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306458 (s : real -> Prop) (c : real) : (term281 s c) = (term282 s c).
Proof. exact (MK_COMB (@lem5306457) (@lem5306456 s c)). Qed.
Lemma lem5306459 (x : real -> real) (s : real -> Prop) (c : real) : (term278 s c x) = (term267 x s c).
Proof. exact (eq_refl (term278 s c x)). Qed.
Lemma lem5306460 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306461 (x : real -> real) (s : real -> Prop) (c : real) : (term283 s c x) = (term284 x s c).
Proof. exact (MK_COMB (@lem5306460 s) (@lem5306459 x s c)). Qed.
Lemma lem5306462 (s : real -> Prop) (c : real) : (term285 s c) = (term286 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306461 x s c)). Qed.
Lemma lem5306463 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306464 (s : real -> Prop) (c : real) : (term277 s c) = (term287 s c).
Proof. exact (MK_COMB (@lem5306463) (@lem5306462 s c)). Qed.
Lemma lem5306465 (s : real -> Prop) (c : real) : ((term276 s c) = (term277 s c)) = ((term271 s c) = (term287 s c)).
Proof. exact (MK_COMB (@lem5306458 s c) (@lem5306464 s c)). Qed.
Lemma lem5306466 (s : real -> Prop) (c : real) : (term271 s c) = (term287 s c).
Proof. exact (EQ_MP (@lem5306465 s c) (@lem5306450 s c)). Qed.
Lemma lem5306467 (s : real -> Prop) (c : real) : (term215 s c) = (term287 s c).
Proof. exact (TRANS (@lem5306446 s c) (@lem5306466 s c)). Qed.
Lemma lem5306468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306469 (s : real -> Prop) (c : real) : (term218 s c) = (term288 s c).
Proof. exact (MK_COMB (@lem5306468) (@lem5306467 s c)). Qed.
Lemma lem5306470 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5306471 (s : real -> Prop) (c : real) : (term220 s c) = (term289 s c).
Proof. exact (MK_COMB (@lem5306469 s c) (@lem5306470 s c)). Qed.
Lemma lem5306475 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5306476 (P : type1028) (Q : Prop) : (term254 P Q) = (term255 P Q).
Proof. exact (@lem5306475 (real -> real) P Q). Qed.
Lemma lem5306477 (s : real -> Prop) (c : real) : (term290 s c) = (term291 s c).
Proof. exact (@lem5306476 (term286 s c) (term17 s c)). Qed.
Lemma lem5306478 (x : real -> real) (s : real -> Prop) (c : real) : (term292 s c x) = (term284 x s c).
Proof. exact (eq_refl (term292 s c x)). Qed.
Lemma lem5306479 (s : real -> Prop) (c : real) : (term293 s c) = (term286 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306478 x s c)). Qed.
Lemma lem5306480 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306481 (s : real -> Prop) (c : real) : (term294 s c) = (term287 s c).
Proof. exact (MK_COMB (@lem5306480) (@lem5306479 s c)). Qed.
Lemma lem5306482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306483 (s : real -> Prop) (c : real) : (term295 s c) = (term288 s c).
Proof. exact (MK_COMB (@lem5306482) (@lem5306481 s c)). Qed.
Lemma lem5306484 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5306485 (s : real -> Prop) (c : real) : (term290 s c) = (term289 s c).
Proof. exact (MK_COMB (@lem5306483 s c) (@lem5306484 s c)). Qed.
Lemma lem5306486 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306487 (s : real -> Prop) (c : real) : (term296 s c) = (term297 s c).
Proof. exact (MK_COMB (@lem5306486) (@lem5306485 s c)). Qed.
Lemma lem5306488 (x : real -> real) (s : real -> Prop) (c : real) : (term292 s c x) = (term284 x s c).
Proof. exact (eq_refl (term292 s c x)). Qed.
Lemma lem5306489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306490 (x : real -> real) (s : real -> Prop) (c : real) : (term298 s c x) = (term299 x s c).
Proof. exact (MK_COMB (@lem5306489) (@lem5306488 x s c)). Qed.
Lemma lem5306491 (s : real -> Prop) (c : real) : (term17 s c) = (term17 s c).
Proof. exact (eq_refl (term17 s c)). Qed.
Lemma lem5306492 (x : real -> real) (s : real -> Prop) (c : real) : (term300 x s c) = (term301 x s c).
Proof. exact (MK_COMB (@lem5306490 x s c) (@lem5306491 s c)). Qed.
Lemma lem5306493 (s : real -> Prop) (c : real) : (term302 s c) = (term303 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306492 x s c)). Qed.
Lemma lem5306494 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306495 (s : real -> Prop) (c : real) : (term291 s c) = (term304 s c).
Proof. exact (MK_COMB (@lem5306494) (@lem5306493 s c)). Qed.
Lemma lem5306496 (s : real -> Prop) (c : real) : ((term290 s c) = (term291 s c)) = ((term289 s c) = (term304 s c)).
Proof. exact (MK_COMB (@lem5306487 s c) (@lem5306495 s c)). Qed.
Lemma lem5306497 (s : real -> Prop) (c : real) : (term289 s c) = (term304 s c).
Proof. exact (EQ_MP (@lem5306496 s c) (@lem5306477 s c)). Qed.
Lemma lem5306499 {A : Type'} (P : Prop) (Q : A -> Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5306500 (P : Prop) (Q : real -> Prop) : (term305 P Q) = (term306 P Q).
Proof. exact (@lem5306499 real P Q). Qed.
Lemma lem5306501 (x : real -> real) (s : real -> Prop) (c : real) : (term307 x s c) = (term308 x s c).
Proof. exact (@lem5306500 (term284 x s c) (term45 s c)). Qed.
Lemma lem5306502 (s : real -> Prop) (x : real) (c : real) : (term78 s c x) = (term44 s x c).
Proof. exact (eq_refl (term78 s c x)). Qed.
Lemma lem5306503 (s : real -> Prop) (c : real) : (term309 s c) = (term45 s c).
Proof. exact (fun_ext (fun x : real => @lem5306502 s x c)). Qed.
Lemma lem5306504 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306505 (s : real -> Prop) (c : real) : (term310 s c) = (term17 s c).
Proof. exact (MK_COMB (@lem5306504) (@lem5306503 s c)). Qed.
Lemma lem5306506 (x : real -> real) (s : real -> Prop) (c : real) : (term299 x s c) = (term299 x s c).
Proof. exact (eq_refl (term299 x s c)). Qed.
Lemma lem5306507 (x : real -> real) (s : real -> Prop) (c : real) : (term307 x s c) = (term301 x s c).
Proof. exact (MK_COMB (@lem5306506 x s c) (@lem5306505 s c)). Qed.
Lemma lem5306508 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306509 (x : real -> real) (s : real -> Prop) (c : real) : (term311 x s c) = (term312 x s c).
Proof. exact (MK_COMB (@lem5306508) (@lem5306507 x s c)). Qed.
Lemma lem5306510 (s : real -> Prop) (x : real) (c : real) : (term78 s c x) = (term44 s x c).
Proof. exact (eq_refl (term78 s c x)). Qed.
Lemma lem5306511 (x : real -> real) (s : real -> Prop) (c : real) : (term299 x s c) = (term299 x s c).
Proof. exact (eq_refl (term299 x s c)). Qed.
Lemma lem5306512 (x : real -> real) (s : real -> Prop) (x' : real) (c : real) : (term313 x s c x') = (term314 x s x' c).
Proof. exact (MK_COMB (@lem5306511 x s c) (@lem5306510 s x' c)). Qed.
Lemma lem5306513 (x : real -> real) (s : real -> Prop) (c : real) : (term315 x s c) = (term316 x s c).
Proof. exact (fun_ext (fun x' : real => @lem5306512 x s x' c)). Qed.
Lemma lem5306514 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306515 (x : real -> real) (s : real -> Prop) (c : real) : (term308 x s c) = (term317 x s c).
Proof. exact (MK_COMB (@lem5306514) (@lem5306513 x s c)). Qed.
Lemma lem5306516 (x : real -> real) (s : real -> Prop) (c : real) : ((term307 x s c) = (term308 x s c)) = ((term301 x s c) = (term317 x s c)).
Proof. exact (MK_COMB (@lem5306509 x s c) (@lem5306515 x s c)). Qed.
Lemma lem5306517 (x : real -> real) (s : real -> Prop) (c : real) : (term301 x s c) = (term317 x s c).
Proof. exact (EQ_MP (@lem5306516 x s c) (@lem5306501 x s c)). Qed.
Lemma lem5306518 (s : real -> Prop) (c : real) : (term303 s c) = (term318 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306517 x s c)). Qed.
Lemma lem5306519 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306520 (s : real -> Prop) (c : real) : (term304 s c) = (term319 s c).
Proof. exact (MK_COMB (@lem5306519) (@lem5306518 s c)). Qed.
Lemma lem5306521 (s : real -> Prop) (c : real) : (term289 s c) = (term319 s c).
Proof. exact (TRANS (@lem5306497 s c) (@lem5306520 s c)). Qed.
Lemma lem5306522 (s : real -> Prop) (c : real) : (term220 s c) = (term319 s c).
Proof. exact (TRANS (@lem5306471 s c) (@lem5306521 s c)). Qed.
Lemma lem5306523 (s : real -> Prop) : (term221 s) = (term320 s).
Proof. exact (fun_ext (fun c : real => @lem5306522 s c)). Qed.
Lemma lem5306524 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306525 (s : real -> Prop) : (term222 s) = (term321 s).
Proof. exact (MK_COMB (@lem5306524) (@lem5306523 s)). Qed.
Lemma lem5306527 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5306528 (P : type1618) : (term322 P) = (term323 P).
Proof. exact (@lem5306527 real (real -> real) P). Qed.
Lemma lem5306529 (s : real -> Prop) : (term324 s) = (term325 s).
Proof. exact (@lem5306528 (term326 s)). Qed.
Lemma lem5306530 (s : real -> Prop) (c : real) : (term327 s c) = (term318 s c).
Proof. exact (eq_refl (term327 s c)). Qed.
Lemma lem5306531 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5306532 (s : real -> Prop) (c : real) (x : real -> real) : (term328 s c x) = (term329 s c x).
Proof. exact (MK_COMB (@lem5306530 s c) (@lem5306531 x)). Qed.
Lemma lem5306533 (x : real -> real) (s : real -> Prop) (c : real) : (term329 s c x) = (term317 x s c).
Proof. exact (eq_refl (term329 s c x)). Qed.
Lemma lem5306534 (x : real -> real) (s : real -> Prop) (c : real) : (term328 s c x) = (term317 x s c).
Proof. exact (TRANS (@lem5306532 s c x) (@lem5306533 x s c)). Qed.
Lemma lem5306535 (s : real -> Prop) (c : real) : (term330 s c) = (term318 s c).
Proof. exact (fun_ext (fun x : real -> real => @lem5306534 x s c)). Qed.
Lemma lem5306536 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306537 (s : real -> Prop) (c : real) : (term331 s c) = (term319 s c).
Proof. exact (MK_COMB (@lem5306536) (@lem5306535 s c)). Qed.
Lemma lem5306538 (s : real -> Prop) : (term332 s) = (term320 s).
Proof. exact (fun_ext (fun c : real => @lem5306537 s c)). Qed.
Lemma lem5306539 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306540 (s : real -> Prop) : (term324 s) = (term321 s).
Proof. exact (MK_COMB (@lem5306539) (@lem5306538 s)). Qed.
Lemma lem5306541 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306542 (s : real -> Prop) : (term333 s) = (term334 s).
Proof. exact (MK_COMB (@lem5306541) (@lem5306540 s)). Qed.
Lemma lem5306543 (s : real -> Prop) (c : real) : (term327 s c) = (term318 s c).
Proof. exact (eq_refl (term327 s c)). Qed.
Lemma lem5306544 (x : type1627) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5306545 (s : real -> Prop) (x : type1627) (c : real) : (term335 s x c) = (term336 s x c).
Proof. exact (MK_COMB (@lem5306543 s c) (@lem5306544 x c)). Qed.
Lemma lem5306546 (x : type1627) (s : real -> Prop) (c : real) : (term336 s x c) = (term337 x s c).
Proof. exact (eq_refl (term336 s x c)). Qed.
Lemma lem5306547 (x : type1627) (s : real -> Prop) (c : real) : (term335 s x c) = (term337 x s c).
Proof. exact (TRANS (@lem5306545 s x c) (@lem5306546 x s c)). Qed.
Lemma lem5306548 (x : type1627) (s : real -> Prop) : (term338 s x) = (term339 x s).
Proof. exact (fun_ext (fun c : real => @lem5306547 x s c)). Qed.
Lemma lem5306549 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306550 (x : type1627) (s : real -> Prop) : (term340 s x) = (term341 x s).
Proof. exact (MK_COMB (@lem5306549) (@lem5306548 x s)). Qed.
Lemma lem5306551 (s : real -> Prop) : (term342 s) = (term343 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5306550 x s)). Qed.
Lemma lem5306552 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5306553 (s : real -> Prop) : (term325 s) = (term344 s).
Proof. exact (MK_COMB (@lem5306552) (@lem5306551 s)). Qed.
Lemma lem5306554 (s : real -> Prop) : ((term324 s) = (term325 s)) = ((term321 s) = (term344 s)).
Proof. exact (MK_COMB (@lem5306542 s) (@lem5306553 s)). Qed.
Lemma lem5306555 (s : real -> Prop) : (term321 s) = (term344 s).
Proof. exact (EQ_MP (@lem5306554 s) (@lem5306529 s)). Qed.
Lemma lem5306557 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5306558 (P : type1626) : (term227 P) = (term228 P).
Proof. exact (@lem5306557 real real P). Qed.
Lemma lem5306559 (x : type1627) (s : real -> Prop) : (term345 x s) = (term346 x s).
Proof. exact (@lem5306558 (term347 x s)). Qed.
Lemma lem5306560 (x : type1627) (s : real -> Prop) (c : real) : (term348 x s c) = (term349 x s c).
Proof. exact (eq_refl (term348 x s c)). Qed.
Lemma lem5306561 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5306562 (x : type1627) (s : real -> Prop) (c : real) (x' : real) : (term350 x s c x') = (term351 x s c x').
Proof. exact (MK_COMB (@lem5306560 x s c) (@lem5306561 x')). Qed.
Lemma lem5306563 (x : type1627) (s : real -> Prop) (x' : real) (c : real) : (term351 x s c x') = (term352 x s x' c).
Proof. exact (eq_refl (term351 x s c x')). Qed.
Lemma lem5306564 (x : type1627) (s : real -> Prop) (x' : real) (c : real) : (term350 x s c x') = (term352 x s x' c).
Proof. exact (TRANS (@lem5306562 x s c x') (@lem5306563 x s x' c)). Qed.
Lemma lem5306565 (x : type1627) (s : real -> Prop) (c : real) : (term353 x s c) = (term349 x s c).
Proof. exact (fun_ext (fun x' : real => @lem5306564 x s x' c)). Qed.
Lemma lem5306566 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem5306567 (x : type1627) (s : real -> Prop) (c : real) : (term354 x s c) = (term337 x s c).
Proof. exact (MK_COMB (@lem5306566) (@lem5306565 x s c)). Qed.
Lemma lem5306568 (x : type1627) (s : real -> Prop) : (term355 x s) = (term339 x s).
Proof. exact (fun_ext (fun c : real => @lem5306567 x s c)). Qed.
Lemma lem5306569 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306570 (x : type1627) (s : real -> Prop) : (term345 x s) = (term341 x s).
Proof. exact (MK_COMB (@lem5306569) (@lem5306568 x s)). Qed.
Lemma lem5306571 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306572 (x : type1627) (s : real -> Prop) : (term356 x s) = (term357 x s).
Proof. exact (MK_COMB (@lem5306571) (@lem5306570 x s)). Qed.
Lemma lem5306573 (x : type1627) (s : real -> Prop) (c : real) : (term348 x s c) = (term349 x s c).
Proof. exact (eq_refl (term348 x s c)). Qed.
Lemma lem5306574 (x : real -> real) (c : real) : (x c) = (x c).
Proof. exact (eq_refl (x c)). Qed.
Lemma lem5306575 (x : type1627) (s : real -> Prop) (x' : real -> real) (c : real) : (term358 x s x' c) = (term359 x s x' c).
Proof. exact (MK_COMB (@lem5306573 x s c) (@lem5306574 x' c)). Qed.
Lemma lem5306576 (x : type1627) (s : real -> Prop) (x' : real -> real) (c : real) : (term359 x s x' c) = (term360 x s x' c).
Proof. exact (eq_refl (term359 x s x' c)). Qed.
Lemma lem5306577 (x : type1627) (s : real -> Prop) (x' : real -> real) (c : real) : (term358 x s x' c) = (term360 x s x' c).
Proof. exact (TRANS (@lem5306575 x s x' c) (@lem5306576 x s x' c)). Qed.
Lemma lem5306578 (x : type1627) (s : real -> Prop) (x' : real -> real) : (term361 x s x') = (term362 x s x').
Proof. exact (fun_ext (fun c : real => @lem5306577 x s x' c)). Qed.
Lemma lem5306579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306580 (x : type1627) (s : real -> Prop) (x' : real -> real) : (term363 x s x') = (term364 x s x').
Proof. exact (MK_COMB (@lem5306579) (@lem5306578 x s x')). Qed.
Lemma lem5306581 (x : type1627) (s : real -> Prop) : (term365 x s) = (term366 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5306580 x s x')). Qed.
Lemma lem5306582 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306583 (x : type1627) (s : real -> Prop) : (term346 x s) = (term367 x s).
Proof. exact (MK_COMB (@lem5306582) (@lem5306581 x s)). Qed.
Lemma lem5306584 (x : type1627) (s : real -> Prop) : ((term345 x s) = (term346 x s)) = ((term341 x s) = (term367 x s)).
Proof. exact (MK_COMB (@lem5306572 x s) (@lem5306583 x s)). Qed.
Lemma lem5306585 (x : type1627) (s : real -> Prop) : (term341 x s) = (term367 x s).
Proof. exact (EQ_MP (@lem5306584 x s) (@lem5306559 x s)). Qed.
Lemma lem5306586 (s : real -> Prop) : (term343 s) = (term368 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5306585 x s)). Qed.
Lemma lem5306587 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5306588 (s : real -> Prop) : (term344 s) = (term369 s).
Proof. exact (MK_COMB (@lem5306587) (@lem5306586 s)). Qed.
Lemma lem5306589 (s : real -> Prop) : (term321 s) = (term369 s).
Proof. exact (TRANS (@lem5306555 s) (@lem5306588 s)). Qed.
Lemma lem5306590 (s : real -> Prop) : (term222 s) = (term369 s).
Proof. exact (TRANS (@lem5306525 s) (@lem5306589 s)). Qed.
Lemma lem5306591 : term223 = term370.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306590 s)). Qed.
Lemma lem5306592 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306593 : term224 = term371.
Proof. exact (MK_COMB (@lem5306592) (@lem5306591)). Qed.
Lemma lem5306595 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5306596 (P : type1016) : (term372 P) = (term373 P).
Proof. exact (@lem5306595 (real -> Prop) type1627 P). Qed.
Lemma lem5306597 : term374 = term375.
Proof. exact (@lem5306596 term376). Qed.
Lemma lem5306598 (s : real -> Prop) : (term377 s) = (term368 s).
Proof. exact (eq_refl (term377 s)). Qed.
Lemma lem5306599 (x : type1627) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5306600 (s : real -> Prop) (x : type1627) : (term378 s x) = (term379 s x).
Proof. exact (MK_COMB (@lem5306598 s) (@lem5306599 x)). Qed.
Lemma lem5306601 (x : type1627) (s : real -> Prop) : (term379 s x) = (term367 x s).
Proof. exact (eq_refl (term379 s x)). Qed.
Lemma lem5306602 (x : type1627) (s : real -> Prop) : (term378 s x) = (term367 x s).
Proof. exact (TRANS (@lem5306600 s x) (@lem5306601 x s)). Qed.
Lemma lem5306603 (s : real -> Prop) : (term380 s) = (term368 s).
Proof. exact (fun_ext (fun x : type1627 => @lem5306602 x s)). Qed.
Lemma lem5306604 : (@ex (real -> real -> real)) = (@ex (real -> real -> real)).
Proof. exact (eq_refl (@ex (real -> real -> real))). Qed.
Lemma lem5306605 (s : real -> Prop) : (term381 s) = (term369 s).
Proof. exact (MK_COMB (@lem5306604) (@lem5306603 s)). Qed.
Lemma lem5306606 : term382 = term370.
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306605 s)). Qed.
Lemma lem5306607 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306608 : term374 = term371.
Proof. exact (MK_COMB (@lem5306607) (@lem5306606)). Qed.
Lemma lem5306609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306610 : term383 = term384.
Proof. exact (MK_COMB (@lem5306609) (@lem5306608)). Qed.
Lemma lem5306611 (s : real -> Prop) : (term377 s) = (term368 s).
Proof. exact (eq_refl (term377 s)). Qed.
Lemma lem5306612 (x : type1019) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5306613 (x : type1019) (s : real -> Prop) : (term385 x s) = (term386 x s).
Proof. exact (MK_COMB (@lem5306611 s) (@lem5306612 x s)). Qed.
Lemma lem5306614 (x : type1019) (s : real -> Prop) : (term386 x s) = (term387 x s).
Proof. exact (eq_refl (term386 x s)). Qed.
Lemma lem5306615 (x : type1019) (s : real -> Prop) : (term385 x s) = (term387 x s).
Proof. exact (TRANS (@lem5306613 x s) (@lem5306614 x s)). Qed.
Lemma lem5306616 (x : type1019) : (term388 x) = (term389 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306615 x s)). Qed.
Lemma lem5306617 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306618 (x : type1019) : (term390 x) = (term391 x).
Proof. exact (MK_COMB (@lem5306617) (@lem5306616 x)). Qed.
Lemma lem5306619 : term392 = term393.
Proof. exact (fun_ext (fun x : type1019 => @lem5306618 x)). Qed.
Lemma lem5306620 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5306621 : term375 = term394.
Proof. exact (MK_COMB (@lem5306620) (@lem5306619)). Qed.
Lemma lem5306622 : (term374 = term375) = (term371 = term394).
Proof. exact (MK_COMB (@lem5306610) (@lem5306621)). Qed.
Lemma lem5306623 : term371 = term394.
Proof. exact (EQ_MP (@lem5306622) (@lem5306597)). Qed.
Lemma lem5306625 {A B : Type'} (P : type1413 A B) : (term225 A B P) = (term226 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem5306626 (P : type1017) : (term395 P) = (term396 P).
Proof. exact (@lem5306625 (real -> Prop) (real -> real) P). Qed.
Lemma lem5306627 (x : type1019) : (term397 x) = (term398 x).
Proof. exact (@lem5306626 (term399 x)). Qed.
Lemma lem5306628 (x : type1019) (s : real -> Prop) : (term400 x s) = (term401 x s).
Proof. exact (eq_refl (term400 x s)). Qed.
Lemma lem5306629 (x : real -> real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem5306630 (x : type1019) (s : real -> Prop) (x' : real -> real) : (term402 x s x') = (term403 x s x').
Proof. exact (MK_COMB (@lem5306628 x s) (@lem5306629 x')). Qed.
Lemma lem5306631 (x : type1019) (s : real -> Prop) (x' : real -> real) : (term403 x s x') = (term404 x s x').
Proof. exact (eq_refl (term403 x s x')). Qed.
Lemma lem5306632 (x : type1019) (s : real -> Prop) (x' : real -> real) : (term402 x s x') = (term404 x s x').
Proof. exact (TRANS (@lem5306630 x s x') (@lem5306631 x s x')). Qed.
Lemma lem5306633 (x : type1019) (s : real -> Prop) : (term405 x s) = (term401 x s).
Proof. exact (fun_ext (fun x' : real -> real => @lem5306632 x s x')). Qed.
Lemma lem5306634 : (@ex (real -> real)) = (@ex (real -> real)).
Proof. exact (eq_refl (@ex (real -> real))). Qed.
Lemma lem5306635 (x : type1019) (s : real -> Prop) : (term406 x s) = (term387 x s).
Proof. exact (MK_COMB (@lem5306634) (@lem5306633 x s)). Qed.
Lemma lem5306636 (x : type1019) : (term407 x) = (term389 x).
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306635 x s)). Qed.
Lemma lem5306637 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306638 (x : type1019) : (term397 x) = (term391 x).
Proof. exact (MK_COMB (@lem5306637) (@lem5306636 x)). Qed.
Lemma lem5306639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306640 (x : type1019) : (term408 x) = (term409 x).
Proof. exact (MK_COMB (@lem5306639) (@lem5306638 x)). Qed.
Lemma lem5306641 (x : type1019) (s : real -> Prop) : (term400 x s) = (term401 x s).
Proof. exact (eq_refl (term400 x s)). Qed.
Lemma lem5306642 (x : type1021) (s : real -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem5306643 (x : type1019) (x' : type1021) (s : real -> Prop) : (term410 x x' s) = (term411 x x' s).
Proof. exact (MK_COMB (@lem5306641 x s) (@lem5306642 x' s)). Qed.
Lemma lem5306644 (x : type1019) (x' : type1021) (s : real -> Prop) : (term411 x x' s) = (term412 x x' s).
Proof. exact (eq_refl (term411 x x' s)). Qed.
Lemma lem5306645 (x : type1019) (x' : type1021) (s : real -> Prop) : (term410 x x' s) = (term412 x x' s).
Proof. exact (TRANS (@lem5306643 x x' s) (@lem5306644 x x' s)). Qed.
Lemma lem5306646 (x : type1019) (x' : type1021) : (term413 x x') = (term414 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306645 x x' s)). Qed.
Lemma lem5306647 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306648 (x : type1019) (x' : type1021) : (term415 x x') = (term416 x x').
Proof. exact (MK_COMB (@lem5306647) (@lem5306646 x x')). Qed.
Lemma lem5306649 (x : type1019) : (term417 x) = (term418 x).
Proof. exact (fun_ext (fun x' : type1021 => @lem5306648 x x')). Qed.
Lemma lem5306650 : (@ex ((real -> Prop) -> real -> real)) = (@ex ((real -> Prop) -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real))). Qed.
Lemma lem5306651 (x : type1019) : (term398 x) = (term419 x).
Proof. exact (MK_COMB (@lem5306650) (@lem5306649 x)). Qed.
Lemma lem5306652 (x : type1019) : ((term397 x) = (term398 x)) = ((term391 x) = (term419 x)).
Proof. exact (MK_COMB (@lem5306640 x) (@lem5306651 x)). Qed.
Lemma lem5306653 (x : type1019) : (term391 x) = (term419 x).
Proof. exact (EQ_MP (@lem5306652 x) (@lem5306627 x)). Qed.
Lemma lem5306654 : term393 = term420.
Proof. exact (fun_ext (fun x : type1019 => @lem5306653 x)). Qed.
Lemma lem5306655 : (@ex ((real -> Prop) -> real -> real -> real)) = (@ex ((real -> Prop) -> real -> real -> real)).
Proof. exact (eq_refl (@ex ((real -> Prop) -> real -> real -> real))). Qed.
Lemma lem5306656 : term394 = term421.
Proof. exact (MK_COMB (@lem5306655) (@lem5306654)). Qed.
Lemma lem5306657 : term371 = term421.
Proof. exact (TRANS (@lem5306623) (@lem5306656)). Qed.
Lemma lem5306659 : term224 = term421.
Proof. exact (TRANS (@lem5306593) (@lem5306657)). Qed.
Lemma lem5306660 : term41 = term421.
Proof. exact (TRANS (@lem5306232) (@lem5306659)). Qed.
Lemma lem5306661 (h1 : term41) : term421.
Proof. exact (EQ_MP (@lem5306660) (@lem5305821 h1)). Qed.
Lemma lem5306662 (x : type1019) (h1 : term419 x) : term419 x.
Proof. exact (h1). Qed.
Lemma lem5306663 (x : type1019) (x' : type1021) (h1 : term416 x x') : term416 x x'.
Proof. exact (h1). Qed.
Lemma lem5306664 (s : real -> Prop) (h1 : term186 s) : term186 s.
Proof. exact (h1). Qed.
Lemma lem5306665 (l : real) (s : real -> Prop) (h1 : term184 l s) : term184 l s.
Proof. exact (h1). Qed.
Lemma lem5306666 (l : real) (s : real -> Prop) (c : real) (h1 : term182 l s c) : term182 l s c.
Proof. exact (h1). Qed.
Lemma lem5306667 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term179 b l s c.
Proof. exact (h1). Qed.
Lemma lem5306688 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5306697 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306724 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term423 x s c b) = (term423 x s c b).
Proof. exact (eq_refl (term423 x s c b)). Qed.
Lemma lem5306725 (x : type1019) (s : real -> Prop) (c : real) : (term424 x s c) = (term424 x s c).
Proof. exact (fun_ext (fun b : real => @lem5306724 x s c b)). Qed.
Lemma lem5306726 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306727 (x : type1019) (s : real -> Prop) (c : real) : (term425 x s c) = (term425 x s c).
Proof. exact (MK_COMB (@lem5306726) (@lem5306725 x s c)). Qed.
Lemma lem5306728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306729 (x : type1019) (s : real -> Prop) (c : real) : (term426 x s c) = (term426 x s c).
Proof. exact (MK_COMB (@lem5306728) (@lem5306727 x s c)). Qed.
Lemma lem5306730 (x : type1019) (s : real -> Prop) (c : real) : (term427 x s c) = (term427 x s c).
Proof. exact (MK_COMB (@lem5306729 x s c) (@lem5306697 s c)). Qed.
Lemma lem5306737 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306738 (x : type1019) (s : real -> Prop) (c : real) : (term428 x s c) = (term428 x s c).
Proof. exact (MK_COMB (@lem5306737 s) (@lem5306730 x s c)). Qed.
Lemma lem5306739 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306740 (x : type1019) (s : real -> Prop) (c : real) : (term429 x s c) = (term429 x s c).
Proof. exact (MK_COMB (@lem5306739) (@lem5306738 x s c)). Qed.
Lemma lem5306741 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term430 x x' s c) = (term430 x x' s c).
Proof. exact (MK_COMB (@lem5306740 x s c) (@lem5306688 x' s c)). Qed.
Lemma lem5306742 (x : type1019) (x' : type1021) (s : real -> Prop) : (term431 x x' s) = (term431 x x' s).
Proof. exact (fun_ext (fun c : real => @lem5306741 x x' s c)). Qed.
Lemma lem5306743 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306744 (x : type1019) (x' : type1021) (s : real -> Prop) : (term412 x x' s) = (term412 x x' s).
Proof. exact (MK_COMB (@lem5306743) (@lem5306742 x x' s)). Qed.
Lemma lem5306745 (x : type1019) (x' : type1021) : (term414 x x') = (term414 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306744 x x' s)). Qed.
Lemma lem5306746 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306747 (x : type1019) (x' : type1021) : (term416 x x') = (term416 x x').
Proof. exact (MK_COMB (@lem5306746) (@lem5306745 x x')). Qed.
Lemma lem5306748 (x : type1019) (x' : type1021) (h1 : term416 x x') : term416 x x'.
Proof. exact (EQ_MP (@lem5306747 x x') (@lem5306663 x x' h1)). Qed.
Lemma lem5306765 (s : real -> Prop) (x : real) (c : real) : (term73 s x c) = (term73 s x c).
Proof. exact (eq_refl (term73 s x c)). Qed.
Lemma lem5306766 (s : real -> Prop) (c : real) : (term81 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5306765 s x c)). Qed.
Lemma lem5306767 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306768 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (MK_COMB (@lem5306767) (@lem5306766 s c)). Qed.
Lemma lem5306773 (l : real) (c : real) : (real_lt l c) = (real_lt l c).
Proof. exact (eq_refl (real_lt l c)). Qed.
Lemma lem5306780 (s : real -> Prop) (l : real) : ((inf s) = l) = ((inf s) = l).
Proof. exact (eq_refl ((inf s) = l)). Qed.
Lemma lem5306795 (s : real -> Prop) (b : real) (x : real) : (term62 s b x) = (term62 s b x).
Proof. exact (eq_refl (term62 s b x)). Qed.
Lemma lem5306796 (s : real -> Prop) (b : real) : (term63 s b) = (term63 s b).
Proof. exact (fun_ext (fun x : real => @lem5306795 s b x)). Qed.
Lemma lem5306797 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306798 (s : real -> Prop) (b : real) : (term64 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5306797) (@lem5306796 s b)). Qed.
Lemma lem5306799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306800 (s : real -> Prop) (b : real) : (term125 s b) = (term125 s b).
Proof. exact (MK_COMB (@lem5306799) (@lem5306798 s b)). Qed.
Lemma lem5306801 (b : real) (s : real -> Prop) (l : real) : (term127 b s l) = (term127 b s l).
Proof. exact (MK_COMB (@lem5306800 s b) (@lem5306780 s l)). Qed.
Lemma lem5306810 (s : real -> Prop) : (term54 s) = (term54 s).
Proof. exact (eq_refl (term54 s)). Qed.
Lemma lem5306811 (b : real) (s : real -> Prop) (l : real) : (term145 b s l) = (term145 b s l).
Proof. exact (MK_COMB (@lem5306810 s) (@lem5306801 b s l)). Qed.
Lemma lem5306812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306813 (b : real) (s : real -> Prop) (l : real) : (term160 b s l) = (term160 b s l).
Proof. exact (MK_COMB (@lem5306812) (@lem5306811 b s l)). Qed.
Lemma lem5306814 (b : real) (s : real -> Prop) (l : real) (c : real) : (term162 b s l c) = (term162 b s l c).
Proof. exact (MK_COMB (@lem5306813 b s l) (@lem5306773 l c)). Qed.
Lemma lem5306815 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306816 (b : real) (s : real -> Prop) (l : real) (c : real) : (term177 b s l c) = (term177 b s l c).
Proof. exact (MK_COMB (@lem5306815) (@lem5306814 b s l c)). Qed.
Lemma lem5306817 (b : real) (l : real) (s : real -> Prop) (c : real) : (term179 b l s c) = (term179 b l s c).
Proof. exact (MK_COMB (@lem5306816 b s l c) (@lem5306768 s c)). Qed.
Lemma lem5306818 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term179 b l s c.
Proof. exact (EQ_MP (@lem5306817 b l s c) (@lem5306667 b l s c h1)). Qed.
Lemma lem5306819 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term82 s c.
Proof. exact (proj2 (@lem5306818 b l s c h1)). Qed.
Lemma lem5306820 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term162 b s l c.
Proof. exact (proj1 (@lem5306818 b l s c h1)). Qed.
Lemma lem5306822 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term145 b s l.
Proof. exact (proj1 (@lem5306820 b l s c h1)). Qed.
Lemma lem5306823 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term127 b s l.
Proof. exact (proj2 (@lem5306822 b l s c h1)). Qed.
Lemma lem5306826 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term64 s b.
Proof. exact (proj1 (@lem5306823 b l s c h1)). Qed.
Lemma lem5306828 {A : Type'} (P : A -> Prop) (Q : Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5306829 (P : real -> Prop) (Q : Prop) : (term434 P Q) = (term435 P Q).
Proof. exact (@lem5306828 real P Q). Qed.
Lemma lem5306830 (x : type1019) (s : real -> Prop) (c : real) : (term436 x s c) = (term437 x s c).
Proof. exact (@lem5306829 (term424 x s c) (term206 s c)). Qed.
Lemma lem5306831 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term438 x s c b) = (term423 x s c b).
Proof. exact (eq_refl (term438 x s c b)). Qed.
Lemma lem5306832 (x : type1019) (s : real -> Prop) (c : real) : (term439 x s c) = (term424 x s c).
Proof. exact (fun_ext (fun b : real => @lem5306831 x s c b)). Qed.
Lemma lem5306833 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306834 (x : type1019) (s : real -> Prop) (c : real) : (term440 x s c) = (term425 x s c).
Proof. exact (MK_COMB (@lem5306833) (@lem5306832 x s c)). Qed.
Lemma lem5306835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306836 (x : type1019) (s : real -> Prop) (c : real) : (term441 x s c) = (term426 x s c).
Proof. exact (MK_COMB (@lem5306835) (@lem5306834 x s c)). Qed.
Lemma lem5306837 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306838 (x : type1019) (s : real -> Prop) (c : real) : (term436 x s c) = (term427 x s c).
Proof. exact (MK_COMB (@lem5306836 x s c) (@lem5306837 s c)). Qed.
Lemma lem5306839 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306840 (x : type1019) (s : real -> Prop) (c : real) : (term442 x s c) = (term443 x s c).
Proof. exact (MK_COMB (@lem5306839) (@lem5306838 x s c)). Qed.
Lemma lem5306841 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term438 x s c b) = (term423 x s c b).
Proof. exact (eq_refl (term438 x s c b)). Qed.
Lemma lem5306842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306843 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term444 x s c b) = (term445 x s c b).
Proof. exact (MK_COMB (@lem5306842) (@lem5306841 x s c b)). Qed.
Lemma lem5306844 (s : real -> Prop) (c : real) : (term206 s c) = (term206 s c).
Proof. exact (eq_refl (term206 s c)). Qed.
Lemma lem5306845 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term446 x b s c) = (term447 x b s c).
Proof. exact (MK_COMB (@lem5306843 x s c b) (@lem5306844 s c)). Qed.
Lemma lem5306846 (x : type1019) (s : real -> Prop) (c : real) : (term448 x s c) = (term449 x s c).
Proof. exact (fun_ext (fun b : real => @lem5306845 x b s c)). Qed.
Lemma lem5306847 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306848 (x : type1019) (s : real -> Prop) (c : real) : (term437 x s c) = (term450 x s c).
Proof. exact (MK_COMB (@lem5306847) (@lem5306846 x s c)). Qed.
Lemma lem5306849 (x : type1019) (s : real -> Prop) (c : real) : ((term436 x s c) = (term437 x s c)) = ((term427 x s c) = (term450 x s c)).
Proof. exact (MK_COMB (@lem5306840 x s c) (@lem5306848 x s c)). Qed.
Lemma lem5306850 (x : type1019) (s : real -> Prop) (c : real) : (term427 x s c) = (term450 x s c).
Proof. exact (EQ_MP (@lem5306849 x s c) (@lem5306830 x s c)). Qed.
Lemma lem5306851 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306852 (x : type1019) (s : real -> Prop) (c : real) : (term428 x s c) = (term451 x s c).
Proof. exact (MK_COMB (@lem5306851 s) (@lem5306850 x s c)). Qed.
Lemma lem5306854 {A : Type'} (P : Prop) (Q : A -> Prop) : (term452 A P Q) = (term453 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem5306855 (P : Prop) (Q : real -> Prop) : (term454 P Q) = (term455 P Q).
Proof. exact (@lem5306854 real P Q). Qed.
Lemma lem5306856 (x : type1019) (s : real -> Prop) (c : real) : (term456 x s c) = (term457 x s c).
Proof. exact (@lem5306855 (s = (@EMPTY real)) (term449 x s c)). Qed.
Lemma lem5306857 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term458 x s c b) = (term447 x b s c).
Proof. exact (eq_refl (term458 x s c b)). Qed.
Lemma lem5306858 (x : type1019) (s : real -> Prop) (c : real) : (term459 x s c) = (term449 x s c).
Proof. exact (fun_ext (fun b : real => @lem5306857 x b s c)). Qed.
Lemma lem5306859 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306860 (x : type1019) (s : real -> Prop) (c : real) : (term460 x s c) = (term450 x s c).
Proof. exact (MK_COMB (@lem5306859) (@lem5306858 x s c)). Qed.
Lemma lem5306861 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306862 (x : type1019) (s : real -> Prop) (c : real) : (term456 x s c) = (term451 x s c).
Proof. exact (MK_COMB (@lem5306861 s) (@lem5306860 x s c)). Qed.
Lemma lem5306863 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306864 (x : type1019) (s : real -> Prop) (c : real) : (term461 x s c) = (term462 x s c).
Proof. exact (MK_COMB (@lem5306863) (@lem5306862 x s c)). Qed.
Lemma lem5306865 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term458 x s c b) = (term447 x b s c).
Proof. exact (eq_refl (term458 x s c b)). Qed.
Lemma lem5306866 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306867 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term463 x s c b) = (term464 x b s c).
Proof. exact (MK_COMB (@lem5306866 s) (@lem5306865 x b s c)). Qed.
Lemma lem5306868 (x : type1019) (s : real -> Prop) (c : real) : (term465 x s c) = (term466 x s c).
Proof. exact (fun_ext (fun b : real => @lem5306867 x b s c)). Qed.
Lemma lem5306869 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306870 (x : type1019) (s : real -> Prop) (c : real) : (term457 x s c) = (term467 x s c).
Proof. exact (MK_COMB (@lem5306869) (@lem5306868 x s c)). Qed.
Lemma lem5306871 (x : type1019) (s : real -> Prop) (c : real) : ((term456 x s c) = (term457 x s c)) = ((term451 x s c) = (term467 x s c)).
Proof. exact (MK_COMB (@lem5306864 x s c) (@lem5306870 x s c)). Qed.
Lemma lem5306872 (x : type1019) (s : real -> Prop) (c : real) : (term451 x s c) = (term467 x s c).
Proof. exact (EQ_MP (@lem5306871 x s c) (@lem5306856 x s c)). Qed.
Lemma lem5306873 (x : type1019) (s : real -> Prop) (c : real) : (term428 x s c) = (term467 x s c).
Proof. exact (TRANS (@lem5306852 x s c) (@lem5306872 x s c)). Qed.
Lemma lem5306874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306875 (x : type1019) (s : real -> Prop) (c : real) : (term429 x s c) = (term468 x s c).
Proof. exact (MK_COMB (@lem5306874) (@lem5306873 x s c)). Qed.
Lemma lem5306876 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5306877 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term430 x x' s c) = (term469 x x' s c).
Proof. exact (MK_COMB (@lem5306875 x s c) (@lem5306876 x' s c)). Qed.
Lemma lem5306879 {A : Type'} (P : A -> Prop) (Q : Prop) : (term432 A P Q) = (term433 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem5306880 (P : real -> Prop) (Q : Prop) : (term434 P Q) = (term435 P Q).
Proof. exact (@lem5306879 real P Q). Qed.
Lemma lem5306881 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term470 x x' s c) = (term471 x x' s c).
Proof. exact (@lem5306880 (term466 x s c) (term422 x' s c)). Qed.
Lemma lem5306882 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term472 x s c b) = (term464 x b s c).
Proof. exact (eq_refl (term472 x s c b)). Qed.
Lemma lem5306883 (x : type1019) (s : real -> Prop) (c : real) : (term473 x s c) = (term466 x s c).
Proof. exact (fun_ext (fun b : real => @lem5306882 x b s c)). Qed.
Lemma lem5306884 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306885 (x : type1019) (s : real -> Prop) (c : real) : (term474 x s c) = (term467 x s c).
Proof. exact (MK_COMB (@lem5306884) (@lem5306883 x s c)). Qed.
Lemma lem5306886 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306887 (x : type1019) (s : real -> Prop) (c : real) : (term475 x s c) = (term468 x s c).
Proof. exact (MK_COMB (@lem5306886) (@lem5306885 x s c)). Qed.
Lemma lem5306888 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5306889 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term470 x x' s c) = (term469 x x' s c).
Proof. exact (MK_COMB (@lem5306887 x s c) (@lem5306888 x' s c)). Qed.
Lemma lem5306890 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5306891 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term476 x x' s c) = (term477 x x' s c).
Proof. exact (MK_COMB (@lem5306890) (@lem5306889 x x' s c)). Qed.
Lemma lem5306892 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term472 x s c b) = (term464 x b s c).
Proof. exact (eq_refl (term472 x s c b)). Qed.
Lemma lem5306893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306894 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term478 x s c b) = (term479 x b s c).
Proof. exact (MK_COMB (@lem5306893) (@lem5306892 x b s c)). Qed.
Lemma lem5306895 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5306896 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term480 x b x' s c) = (term481 x b x' s c).
Proof. exact (MK_COMB (@lem5306894 x b s c) (@lem5306895 x' s c)). Qed.
Lemma lem5306897 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term482 x x' s c) = (term483 x x' s c).
Proof. exact (fun_ext (fun b : real => @lem5306896 x b x' s c)). Qed.
Lemma lem5306898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306899 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term471 x x' s c) = (term484 x x' s c).
Proof. exact (MK_COMB (@lem5306898) (@lem5306897 x x' s c)). Qed.
Lemma lem5306900 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : ((term470 x x' s c) = (term471 x x' s c)) = ((term469 x x' s c) = (term484 x x' s c)).
Proof. exact (MK_COMB (@lem5306891 x x' s c) (@lem5306899 x x' s c)). Qed.
Lemma lem5306901 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term469 x x' s c) = (term484 x x' s c).
Proof. exact (EQ_MP (@lem5306900 x x' s c) (@lem5306881 x x' s c)). Qed.
Lemma lem5306902 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term430 x x' s c) = (term484 x x' s c).
Proof. exact (TRANS (@lem5306877 x x' s c) (@lem5306901 x x' s c)). Qed.
Lemma lem5306903 (x : type1019) (x' : type1021) (s : real -> Prop) : (term431 x x' s) = (term485 x x' s).
Proof. exact (fun_ext (fun c : real => @lem5306902 x x' s c)). Qed.
Lemma lem5306904 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306905 (x : type1019) (x' : type1021) (s : real -> Prop) : (term412 x x' s) = (term486 x x' s).
Proof. exact (MK_COMB (@lem5306904) (@lem5306903 x x' s)). Qed.
Lemma lem5306906 (x : type1019) (x' : type1021) : (term414 x x') = (term487 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306905 x x' s)). Qed.
Lemma lem5306907 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306908 (x : type1019) (x' : type1021) : (term416 x x') = (term488 x x').
Proof. exact (MK_COMB (@lem5306907) (@lem5306906 x x')). Qed.
Lemma lem5306913 (x' : type1021) (s : real -> Prop) (c : real) : (term422 x' s c) = (term422 x' s c).
Proof. exact (eq_refl (term422 x' s c)). Qed.
Lemma lem5306930 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term447 x b s c) = (term489 x b s c).
Proof. exact (@lem19699 (term490 x c b s) (term491 x s c b) (term206 s c)). Qed.
Lemma lem5306933 (s : real -> Prop) : (term213 s) = (term213 s).
Proof. exact (eq_refl (term213 s)). Qed.
Lemma lem5306934 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term464 x b s c) = (term492 x b s c).
Proof. exact (MK_COMB (@lem5306933 s) (@lem5306930 x b s c)). Qed.
Lemma lem5306941 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term492 x b s c) = (term493 x b s c).
Proof. exact (@lem19490 (term494 x b s c) (s = (@EMPTY real)) (term495 x b s c)). Qed.
Lemma lem5306942 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term464 x b s c) = (term493 x b s c).
Proof. exact (TRANS (@lem5306934 x b s c) (@lem5306941 x b s c)). Qed.
Lemma lem5306943 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5306944 (x : type1019) (b : real) (s : real -> Prop) (c : real) : (term479 x b s c) = (term496 x b s c).
Proof. exact (MK_COMB (@lem5306943) (@lem5306942 x b s c)). Qed.
Lemma lem5306945 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term481 x b x' s c) = (term497 x b x' s c).
Proof. exact (MK_COMB (@lem5306944 x b s c) (@lem5306913 x' s c)). Qed.
Lemma lem5306946 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term497 x b x' s c) = (term498 x b x' s c).
Proof. exact (@lem19490 (term499 x' c s) (term493 x b s c) (term500 x' s c)). Qed.
Lemma lem5306953 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term501 x b x' s c) = (term502 x b x' s c).
Proof. exact (@lem19699 (term503 x b s c) (term504 x b s c) (term500 x' s c)). Qed.
Lemma lem5306960 (x : type1019) (b : real) (x' : type1021) (c : real) (s : real -> Prop) : (term505 x b x' c s) = (term506 x b x' c s).
Proof. exact (@lem19699 (term503 x b s c) (term504 x b s c) (term499 x' c s)). Qed.
Lemma lem5306961 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5306962 (x : type1019) (b : real) (x' : type1021) (c : real) (s : real -> Prop) : (term507 x b x' c s) = (term508 x b x' c s).
Proof. exact (MK_COMB (@lem5306961) (@lem5306960 x b x' c s)). Qed.
Lemma lem5306963 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term498 x b x' s c) = (term509 x b x' s c).
Proof. exact (MK_COMB (@lem5306962 x b x' c s) (@lem5306953 x b x' s c)). Qed.
Lemma lem5306964 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term497 x b x' s c) = (term509 x b x' s c).
Proof. exact (TRANS (@lem5306946 x b x' s c) (@lem5306963 x b x' s c)). Qed.
Lemma lem5306965 (x : type1019) (b : real) (x' : type1021) (s : real -> Prop) (c : real) : (term481 x b x' s c) = (term509 x b x' s c).
Proof. exact (TRANS (@lem5306945 x b x' s c) (@lem5306964 x b x' s c)). Qed.
Lemma lem5306966 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term483 x x' s c) = (term510 x x' s c).
Proof. exact (fun_ext (fun b : real => @lem5306965 x b x' s c)). Qed.
Lemma lem5306967 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306968 (x : type1019) (x' : type1021) (s : real -> Prop) (c : real) : (term484 x x' s c) = (term511 x x' s c).
Proof. exact (MK_COMB (@lem5306967) (@lem5306966 x x' s c)). Qed.
Lemma lem5306969 (x : type1019) (x' : type1021) (s : real -> Prop) : (term485 x x' s) = (term512 x x' s).
Proof. exact (fun_ext (fun c : real => @lem5306968 x x' s c)). Qed.
Lemma lem5306970 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306971 (x : type1019) (x' : type1021) (s : real -> Prop) : (term486 x x' s) = (term513 x x' s).
Proof. exact (MK_COMB (@lem5306970) (@lem5306969 x x' s)). Qed.
Lemma lem5306972 (x : type1019) (x' : type1021) : (term487 x x') = (term514 x x').
Proof. exact (fun_ext (fun s : real -> Prop => @lem5306971 x x' s)). Qed.
Lemma lem5306973 : (@all (real -> Prop)) = (@all (real -> Prop)).
Proof. exact (eq_refl (@all (real -> Prop))). Qed.
Lemma lem5306974 (x : type1019) (x' : type1021) : (term488 x x') = (term515 x x').
Proof. exact (MK_COMB (@lem5306973) (@lem5306972 x x')). Qed.
Lemma lem5306975 (x : type1019) (x' : type1021) : (term416 x x') = (term515 x x').
Proof. exact (TRANS (@lem5306908 x x') (@lem5306974 x x')). Qed.
Lemma lem5306976 (x : type1019) (x' : type1021) (h1 : term416 x x') : term515 x x'.
Proof. exact (EQ_MP (@lem5306975 x x') (@lem5306748 x x' h1)). Qed.
Lemma lem5306984 (s : real -> Prop) (x : real) (c : real) : (term73 s x c) = (term73 s x c).
Proof. exact (eq_refl (term73 s x c)). Qed.
Lemma lem5306985 (s : real -> Prop) (c : real) : (term81 s c) = (term81 s c).
Proof. exact (fun_ext (fun x : real => @lem5306984 s x c)). Qed.
Lemma lem5306986 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5306988 (s : real -> Prop) (c : real) : (term82 s c) = (term82 s c).
Proof. exact (MK_COMB (@lem5306986) (@lem5306985 s c)). Qed.
Lemma lem5306989 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term82 s c.
Proof. exact (EQ_MP (@lem5306988 s c) (@lem5306819 b l s c h1)). Qed.
Lemma lem5307005 (s : real -> Prop) (b : real) (x : real) : (term62 s b x) = (term62 s b x).
Proof. exact (eq_refl (term62 s b x)). Qed.
Lemma lem5307006 (s : real -> Prop) (b : real) : (term63 s b) = (term63 s b).
Proof. exact (fun_ext (fun x : real => @lem5307005 s b x)). Qed.
Lemma lem5307007 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5307009 (s : real -> Prop) (b : real) : (term64 s b) = (term64 s b).
Proof. exact (MK_COMB (@lem5307007) (@lem5307006 s b)). Qed.
Lemma lem5307010 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term64 s b.
Proof. exact (EQ_MP (@lem5307009 s b) (@lem5306826 b l s c h1)). Qed.
Lemma lem5307015 (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term516 x x' _69580.
Proof. exact (@lem5306976 x x' h1 _69580). Qed.
Lemma lem5307016 (x : type1019) (x' : type1021) (_69580 : real -> Prop) : (term516 x x' _69580) = (term513 x x' _69580).
Proof. exact (eq_refl (term516 x x' _69580)). Qed.
Lemma lem5307017 (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term513 x x' _69580.
Proof. exact (EQ_MP (@lem5307016 x x' _69580) (@lem5307015 _69580 x x' h1)). Qed.
Lemma lem5307018 (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term517 x x' _69580 _69581.
Proof. exact (@lem5307017 _69580 x x' h1 _69581). Qed.
Lemma lem5307019 (x : type1019) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term517 x x' _69580 _69581) = (term511 x x' _69580 _69581).
Proof. exact (eq_refl (term517 x x' _69580 _69581)). Qed.
Lemma lem5307020 (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term511 x x' _69580 _69581.
Proof. exact (EQ_MP (@lem5307019 x x' _69580 _69581) (@lem5307018 _69580 _69581 x x' h1)). Qed.
Lemma lem5307021 (_69580 : real -> Prop) (_69581 : real) (_69582 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term518 x x' _69580 _69581 _69582.
Proof. exact (@lem5307020 _69580 _69581 x x' h1 _69582). Qed.
Lemma lem5307022 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term518 x x' _69580 _69581 _69582) = (term509 x _69582 x' _69580 _69581).
Proof. exact (eq_refl (term518 x x' _69580 _69581 _69582)). Qed.
Lemma lem5307023 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term509 x _69582 x' _69580 _69581.
Proof. exact (EQ_MP (@lem5307022 x _69582 x' _69580 _69581) (@lem5307021 _69580 _69581 _69582 x x' h1)). Qed.
Lemma lem5307024 (_69583 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term519 s c _69583.
Proof. exact (@lem5306989 b l s c h1 _69583). Qed.
Lemma lem5307025 (s : real -> Prop) (_69583 : real) (c : real) : (term519 s c _69583) = (term73 s _69583 c).
Proof. exact (eq_refl (term519 s c _69583)). Qed.
Lemma lem5307027 (_69584 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term520 s b _69584.
Proof. exact (@lem5307010 b l s c h1 _69584). Qed.
Lemma lem5307028 (s : real -> Prop) (b : real) (_69584 : real) : (term520 s b _69584) = (term62 s b _69584).
Proof. exact (eq_refl (term520 s b _69584)). Qed.
Lemma lem5307030 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term502 x _69582 x' _69580 _69581.
Proof. exact (proj2 (@lem5307023 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307031 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term506 x _69582 x' _69581 _69580.
Proof. exact (proj1 (@lem5307023 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307032 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term521 x _69582 x' _69580 _69581.
Proof. exact (proj2 (@lem5307030 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307033 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term522 x _69582 x' _69580 _69581.
Proof. exact (proj1 (@lem5307030 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307034 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term523 x _69582 x' _69581 _69580.
Proof. exact (proj2 (@lem5307031 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307035 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term524 x _69582 x' _69581 _69580.
Proof. exact (proj1 (@lem5307031 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307043 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : real_lt l c.
Proof. exact (proj2 (@lem5306820 b l s c h1)). Qed.
Lemma lem5307053 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : (inf s) = l.
Proof. exact (proj2 (@lem5306823 b l s c h1)). Qed.
Lemma lem5307057 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term522 x _69582 x' _69580 _69581) = (term525 x _69582 x' _69580 _69581).
Proof. exact (@lem5305366 (_69580 = (@EMPTY real)) (term494 x _69582 _69580 _69581) (term500 x' _69580 _69581)). Qed.
Lemma lem5307064 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term526 x _69582 x' _69580 _69581) = (term527 x _69582 x' _69580 _69581).
Proof. exact (@lem5305366 (term490 x _69581 _69582 _69580) (term206 _69580 _69581) (term500 x' _69580 _69581)). Qed.
Lemma lem5307065 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307068 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term525 x _69582 x' _69580 _69581) = (term528 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307065 _69580) (@lem5307064 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307070 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term522 x _69582 x' _69580 _69581) = (term528 x _69582 x' _69580 _69581).
Proof. exact (TRANS (@lem5307057 x _69582 x' _69580 _69581) (@lem5307068 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307075 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term521 x _69582 x' _69580 _69581) = (term529 x _69582 x' _69580 _69581).
Proof. exact (@lem5305366 (_69580 = (@EMPTY real)) (term495 x _69582 _69580 _69581) (term500 x' _69580 _69581)). Qed.
Lemma lem5307082 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term530 x _69582 x' _69580 _69581) = (term531 x _69582 x' _69580 _69581).
Proof. exact (@lem5305366 (term491 x _69580 _69581 _69582) (term206 _69580 _69581) (term500 x' _69580 _69581)). Qed.
Lemma lem5307083 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307086 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term529 x _69582 x' _69580 _69581) = (term532 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307083 _69580) (@lem5307082 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307088 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term521 x _69582 x' _69580 _69581) = (term532 x _69582 x' _69580 _69581).
Proof. exact (TRANS (@lem5307075 x _69582 x' _69580 _69581) (@lem5307086 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307093 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term524 x _69582 x' _69581 _69580) = (term533 x _69582 x' _69581 _69580).
Proof. exact (@lem5305366 (_69580 = (@EMPTY real)) (term494 x _69582 _69580 _69581) (term499 x' _69581 _69580)). Qed.
Lemma lem5307100 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term534 x _69582 x' _69581 _69580) = (term535 x _69582 x' _69581 _69580).
Proof. exact (@lem5305366 (term490 x _69581 _69582 _69580) (term206 _69580 _69581) (term499 x' _69581 _69580)). Qed.
Lemma lem5307101 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307104 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term533 x _69582 x' _69581 _69580) = (term536 x _69582 x' _69581 _69580).
Proof. exact (MK_COMB (@lem5307101 _69580) (@lem5307100 x _69582 x' _69581 _69580)). Qed.
Lemma lem5307106 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term524 x _69582 x' _69581 _69580) = (term536 x _69582 x' _69581 _69580).
Proof. exact (TRANS (@lem5307093 x _69582 x' _69581 _69580) (@lem5307104 x _69582 x' _69581 _69580)). Qed.
Lemma lem5307111 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term523 x _69582 x' _69581 _69580) = (term537 x _69582 x' _69581 _69580).
Proof. exact (@lem5305366 (_69580 = (@EMPTY real)) (term495 x _69582 _69580 _69581) (term499 x' _69581 _69580)). Qed.
Lemma lem5307118 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term538 x _69582 x' _69581 _69580) = (term539 x _69582 x' _69581 _69580).
Proof. exact (@lem5305366 (term491 x _69580 _69581 _69582) (term206 _69580 _69581) (term499 x' _69581 _69580)). Qed.
Lemma lem5307119 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307122 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term537 x _69582 x' _69581 _69580) = (term540 x _69582 x' _69581 _69580).
Proof. exact (MK_COMB (@lem5307119 _69580) (@lem5307118 x _69582 x' _69581 _69580)). Qed.
Lemma lem5307124 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term523 x _69582 x' _69581 _69580) = (term540 x _69582 x' _69581 _69580).
Proof. exact (TRANS (@lem5307111 x _69582 x' _69581 _69580) (@lem5307122 x _69582 x' _69581 _69580)). Qed.
Lemma lem5307126 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : l = (inf s).
Proof. exact (SYM (@lem5307053 b l s c h1)). Qed.
Lemma lem5307154 (_69583 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term73 s _69583 c.
Proof. exact (EQ_MP (@lem5307025 s _69583 c) (@lem5307024 _69583 b l s c h1)). Qed.
Lemma lem5307155 (c : real) : (term541 c) = (term541 c).
Proof. exact (eq_refl (term541 c)). Qed.
Lemma lem5307156 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : (term542 c l) = (term543 c s).
Proof. exact (MK_COMB (@lem5307155 c) (@lem5307126 b l s c h1)). Qed.
Lemma lem5307157 (s : real -> Prop) (c : real) : (term543 c s) = (term46 s c).
Proof. exact (eq_refl (term543 c s)). Qed.
Lemma lem5307158 (c : real) (l : real) : (term544 c l) = (term544 c l).
Proof. exact (eq_refl (term544 c l)). Qed.
Lemma lem5307159 (l : real) (s : real -> Prop) (c : real) : ((term542 c l) = (term543 c s)) = ((term542 c l) = (term46 s c)).
Proof. exact (MK_COMB (@lem5307158 c l) (@lem5307157 s c)). Qed.
Lemma lem5307160 (l : real) (c : real) : (term542 c l) = (real_lt l c).
Proof. exact (eq_refl (term542 c l)). Qed.
Lemma lem5307161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5307162 (l : real) (c : real) : (term544 c l) = (term545 l c).
Proof. exact (MK_COMB (@lem5307161) (@lem5307160 l c)). Qed.
Lemma lem5307163 (s : real -> Prop) (c : real) : (term46 s c) = (term46 s c).
Proof. exact (eq_refl (term46 s c)). Qed.
Lemma lem5307164 (l : real) (s : real -> Prop) (c : real) : ((term542 c l) = (term46 s c)) = ((real_lt l c) = (term46 s c)).
Proof. exact (MK_COMB (@lem5307162 l c) (@lem5307163 s c)). Qed.
Lemma lem5307165 (l : real) (s : real -> Prop) (c : real) : ((term542 c l) = (term543 c s)) = ((real_lt l c) = (term46 s c)).
Proof. exact (TRANS (@lem5307159 l s c) (@lem5307164 l s c)). Qed.
Lemma lem5307166 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : (real_lt l c) = (term46 s c).
Proof. exact (EQ_MP (@lem5307165 l s c) (@lem5307156 b l s c h1)). Qed.
Lemma lem5307195 (_69584 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term62 s b _69584.
Proof. exact (EQ_MP (@lem5307028 s b _69584) (@lem5307027 _69584 b l s c h1)). Qed.
Lemma lem5307209 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term528 x _69582 x' _69580 _69581.
Proof. exact (EQ_MP (@lem5307070 x _69582 x' _69580 _69581) (@lem5307033 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307223 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term532 x _69582 x' _69580 _69581.
Proof. exact (EQ_MP (@lem5307088 x _69582 x' _69580 _69581) (@lem5307032 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307237 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term536 x _69582 x' _69581 _69580.
Proof. exact (EQ_MP (@lem5307106 x _69582 x' _69581 _69580) (@lem5307035 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307251 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term540 x _69582 x' _69581 _69580.
Proof. exact (EQ_MP (@lem5307124 x _69582 x' _69581 _69580) (@lem5307034 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307359 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5306822 b l s c h1)). Qed.
Lemma lem5307360 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5307359 b l s c h1). Qed.
Lemma lem5307362 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5307363 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5307362 (s = (@EMPTY real))). Qed.
Lemma lem5307364 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5307363 s) (@lem5307360 b l s c h1)). Qed.
Lemma lem5307366 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5306822 b l s c h1)). Qed.
Lemma lem5307367 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5307366 b l s c h1). Qed.
Lemma lem5307369 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5307370 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5307369 (s = (@EMPTY real))). Qed.
Lemma lem5307371 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5307370 s) (@lem5307367 b l s c h1)). Qed.
Lemma lem5307373 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307166 b l s c h1) (@lem5307043 b l s c h1)). Qed.
Lemma lem5307374 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 s c.
Proof. exact (fun h0 : term206 s c => @lem5307373 b l s c h1). Qed.
Lemma lem5307376 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307377 (s : real -> Prop) (c : real) : (term548 s c) = (term46 s c).
Proof. exact (@lem5307376 (term46 s c)). Qed.
Lemma lem5307378 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307377 s c) (@lem5307374 b l s c h1)). Qed.
Lemma lem5307381 (x' : type1021) (c : real) (s : real -> Prop) (h1 : term550 x' c s) : term550 x' c s.
Proof. exact (h1). Qed.
Lemma lem5307382 (x' : type1021) (c : real) (s : real -> Prop) (h1 : term550 x' c s) : term551 x' c s.
Proof. exact (fun h0 : term499 x' c s => @lem5307381 x' c s h1). Qed.
Lemma lem5307384 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5307385 (x' : type1021) (c : real) (s : real -> Prop) : (term551 x' c s) = (term550 x' c s).
Proof. exact (@lem5307384 (term499 x' c s)). Qed.
Lemma lem5307386 (x' : type1021) (c : real) (s : real -> Prop) (h1 : term550 x' c s) : term550 x' c s.
Proof. exact (EQ_MP (@lem5307385 x' c s) (@lem5307382 x' c s h1)). Qed.
Lemma lem5307414 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5307415 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term552 x' _69581 _69580) = (term553 x' _69580 _69581).
Proof. exact (@lem5307414 (term499 x' _69581 _69580) (term206 _69580 _69581)). Qed.
Lemma lem5307421 (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term554 x _69581 _69582 _69580) = (term554 x _69581 _69582 _69580).
Proof. exact (eq_refl (term554 x _69581 _69582 _69580)). Qed.
Lemma lem5307422 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term535 x _69582 x' _69581 _69580) = (term555 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307421 x _69581 _69582 _69580) (@lem5307415 x' _69580 _69581)). Qed.
Lemma lem5307433 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307434 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term536 x _69582 x' _69581 _69580) = (term556 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307433 _69580) (@lem5307422 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307445 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5307446 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term557 x _69582 x' _69581 _69580) = (term558 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307445) (@lem5307434 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307450 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5307451 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term559 x _69582 x' _69581 _69580) = (term536 x _69582 x' _69581 _69580).
Proof. exact (@lem5307450 (_69580 = (@EMPTY real)) (term490 x _69581 _69582 _69580) (term552 x' _69581 _69580)). Qed.
Lemma lem5307477 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5307478 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term552 x' _69581 _69580) = (term553 x' _69580 _69581).
Proof. exact (@lem5307477 (term499 x' _69581 _69580) (term206 _69580 _69581)). Qed.
Lemma lem5307484 (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term554 x _69581 _69582 _69580) = (term554 x _69581 _69582 _69580).
Proof. exact (eq_refl (term554 x _69581 _69582 _69580)). Qed.
Lemma lem5307485 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term535 x _69582 x' _69581 _69580) = (term555 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307484 x _69581 _69582 _69580) (@lem5307478 x' _69580 _69581)). Qed.
Lemma lem5307496 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307497 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term536 x _69582 x' _69581 _69580) = (term556 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307496 _69580) (@lem5307485 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307508 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term559 x _69582 x' _69581 _69580) = (term556 x _69582 x' _69580 _69581).
Proof. exact (TRANS (@lem5307451 x _69582 x' _69581 _69580) (@lem5307497 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307509 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : ((term536 x _69582 x' _69581 _69580) = (term559 x _69582 x' _69581 _69580)) = ((term556 x _69582 x' _69580 _69581) = (term556 x _69582 x' _69580 _69581)).
Proof. exact (MK_COMB (@lem5307446 x _69582 x' _69580 _69581) (@lem5307508 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307511 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5307512 (x : Prop) : (x = x) = True.
Proof. exact (@lem5307511 Prop x). Qed.
Lemma lem5307513 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : ((term556 x _69582 x' _69580 _69581) = (term556 x _69582 x' _69580 _69581)) = True.
Proof. exact (@lem5307512 (term556 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307514 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : ((term536 x _69582 x' _69581 _69580) = (term559 x _69582 x' _69581 _69580)) = True.
Proof. exact (TRANS (@lem5307509 x _69582 x' _69580 _69581) (@lem5307513 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307515 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : True = ((term536 x _69582 x' _69581 _69580) = (term559 x _69582 x' _69581 _69580)).
Proof. exact (SYM (@lem5307514 x _69582 x' _69581 _69580)). Qed.
Lemma lem5307516 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term536 x _69582 x' _69581 _69580) = (term559 x _69582 x' _69581 _69580).
Proof. exact (EQ_MP (@lem5307515 x _69582 x' _69581 _69580) (@lem0)). Qed.
Lemma lem5307517 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term559 x _69582 x' _69581 _69580.
Proof. exact (EQ_MP (@lem5307516 x _69582 x' _69581 _69580) (@lem5307237 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307519 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5307520 (x' : type1021) (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term559 x _69582 x' _69581 _69580) = (term561 x' x _69581 _69582 _69580).
Proof. exact (@lem5307519 (term562 x' _69581 _69580) (term490 x _69581 _69582 _69580)). Qed.
Lemma lem5307522 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5307523 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term565 x' _69581 _69580) = (term566 x' _69581 _69580).
Proof. exact (@lem5307522 (_69580 = (@EMPTY real)) (term552 x' _69581 _69580)). Qed.
Lemma lem5307525 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5307526 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term567 x' _69581 _69580) = (term568 x' _69581 _69580).
Proof. exact (@lem5307525 (term206 _69580 _69581) (term499 x' _69581 _69580)). Qed.
Lemma lem5307528 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5307529 (_69580 : real -> Prop) (_69581 : real) : (term570 _69580 _69581) = (term46 _69580 _69581).
Proof. exact (@lem5307528 (term46 _69580 _69581)). Qed.
Lemma lem5307530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5307531 (_69580 : real -> Prop) (_69581 : real) : (term571 _69580 _69581) = (term572 _69580 _69581).
Proof. exact (MK_COMB (@lem5307530) (@lem5307529 _69580 _69581)). Qed.
Lemma lem5307532 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term550 x' _69581 _69580) = (term550 x' _69581 _69580).
Proof. exact (eq_refl (term550 x' _69581 _69580)). Qed.
Lemma lem5307533 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term568 x' _69581 _69580) = (term573 x' _69581 _69580).
Proof. exact (MK_COMB (@lem5307531 _69580 _69581) (@lem5307532 x' _69581 _69580)). Qed.
Lemma lem5307534 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term567 x' _69581 _69580) = (term573 x' _69581 _69580).
Proof. exact (TRANS (@lem5307526 x' _69581 _69580) (@lem5307533 x' _69581 _69580)). Qed.
Lemma lem5307535 (_69580 : real -> Prop) : (term54 _69580) = (term54 _69580).
Proof. exact (eq_refl (term54 _69580)). Qed.
Lemma lem5307536 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term566 x' _69581 _69580) = (term574 x' _69581 _69580).
Proof. exact (MK_COMB (@lem5307535 _69580) (@lem5307534 x' _69581 _69580)). Qed.
Lemma lem5307537 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term565 x' _69581 _69580) = (term574 x' _69581 _69580).
Proof. exact (TRANS (@lem5307523 x' _69581 _69580) (@lem5307536 x' _69581 _69580)). Qed.
Lemma lem5307538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5307539 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term575 x' _69581 _69580) = (term576 x' _69581 _69580).
Proof. exact (MK_COMB (@lem5307538) (@lem5307537 x' _69581 _69580)). Qed.
Lemma lem5307540 (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term490 x _69581 _69582 _69580) = (term490 x _69581 _69582 _69580).
Proof. exact (eq_refl (term490 x _69581 _69582 _69580)). Qed.
Lemma lem5307541 (x' : type1021) (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term561 x' x _69581 _69582 _69580) = (term577 x' x _69581 _69582 _69580).
Proof. exact (MK_COMB (@lem5307539 x' _69581 _69580) (@lem5307540 x _69581 _69582 _69580)). Qed.
Lemma lem5307542 (x' : type1021) (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term559 x _69582 x' _69581 _69580) = (term577 x' x _69581 _69582 _69580).
Proof. exact (TRANS (@lem5307520 x' x _69581 _69582 _69580) (@lem5307541 x' x _69581 _69582 _69580)). Qed.
Lemma lem5307544 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term550 x' c s) (h2 : term179 b l s c) : term573 x' c s.
Proof. exact (conj (@lem5307378 b l s c h2) (@lem5307386 x' c s h1)). Qed.
Lemma lem5307545 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term550 x' c s) (h2 : term179 b l s c) : term574 x' c s.
Proof. exact (conj (@lem5307371 b l s c h2) (@lem5307544 x' b l s c h1 h2)). Qed.
Lemma lem5307547 (_69581 : real) (_69582 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term577 x' x _69581 _69582 _69580.
Proof. exact (EQ_MP (@lem5307542 x' x _69581 _69582 _69580) (@lem5307517 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307548 (c : real) (_69582 : real) (s : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term577 x' x c _69582 s.
Proof. exact (@lem5307547 c _69582 s x x' h1). Qed.
Lemma lem5307551 (_69582 : real) (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term490 x c _69582 s.
Proof. exact (@lem5307548 c _69582 s x x' h1 (@lem5307545 x' b l s c h2 h3)). Qed.
Lemma lem5307552 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (@lem5307551 b x x' b l s c h1 h2 h3). Qed.
Lemma lem5307553 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term578 x c b s.
Proof. exact (fun h0 : term579 x c b s => @lem5307552 x x' b l s c h1 h2 h3). Qed.
Lemma lem5307555 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307556 (x : type1019) (c : real) (b : real) (s : real -> Prop) : (term578 x c b s) = (term490 x c b s).
Proof. exact (@lem5307555 (term490 x c b s)). Qed.
Lemma lem5307557 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (EQ_MP (@lem5307556 x c b s) (@lem5307553 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307563 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5307564 (b : real) (_69584 : real) (s : real -> Prop) : (term62 s b _69584) = (term580 b _69584 s).
Proof. exact (@lem5307563 (real_le b _69584) (term581 _69584 s)). Qed.
Lemma lem5307570 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5307571 (b : real) (_69584 : real) (s : real -> Prop) : (term582 s b _69584) = (term583 b _69584 s).
Proof. exact (MK_COMB (@lem5307570) (@lem5307564 b _69584 s)). Qed.
Lemma lem5307577 (b : real) (_69584 : real) (s : real -> Prop) : (term580 b _69584 s) = (term580 b _69584 s).
Proof. exact (eq_refl (term580 b _69584 s)). Qed.
Lemma lem5307578 (b : real) (_69584 : real) (s : real -> Prop) : ((term62 s b _69584) = (term580 b _69584 s)) = ((term580 b _69584 s) = (term580 b _69584 s)).
Proof. exact (MK_COMB (@lem5307571 b _69584 s) (@lem5307577 b _69584 s)). Qed.
Lemma lem5307580 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5307581 (x : Prop) : (x = x) = True.
Proof. exact (@lem5307580 Prop x). Qed.
Lemma lem5307582 (b : real) (_69584 : real) (s : real -> Prop) : ((term580 b _69584 s) = (term580 b _69584 s)) = True.
Proof. exact (@lem5307581 (term580 b _69584 s)). Qed.
Lemma lem5307583 (b : real) (_69584 : real) (s : real -> Prop) : ((term62 s b _69584) = (term580 b _69584 s)) = True.
Proof. exact (TRANS (@lem5307578 b _69584 s) (@lem5307582 b _69584 s)). Qed.
Lemma lem5307584 (b : real) (_69584 : real) (s : real -> Prop) : True = ((term62 s b _69584) = (term580 b _69584 s)).
Proof. exact (SYM (@lem5307583 b _69584 s)). Qed.
Lemma lem5307585 (b : real) (_69584 : real) (s : real -> Prop) : (term62 s b _69584) = (term580 b _69584 s).
Proof. exact (EQ_MP (@lem5307584 b _69584 s) (@lem0)). Qed.
Lemma lem5307586 (_69584 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term580 b _69584 s.
Proof. exact (EQ_MP (@lem5307585 b _69584 s) (@lem5307195 _69584 b l s c h1)). Qed.
Lemma lem5307588 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5307589 (s : real -> Prop) (b : real) (_69584 : real) : (term580 b _69584 s) = (term584 s b _69584).
Proof. exact (@lem5307588 (term581 _69584 s) (real_le b _69584)). Qed.
Lemma lem5307591 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5307592 (_69584 : real) (s : real -> Prop) : (term585 _69584 s) = (@IN real _69584 s).
Proof. exact (@lem5307591 (@IN real _69584 s)). Qed.
Lemma lem5307593 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5307594 (_69584 : real) (s : real -> Prop) : (term586 _69584 s) = (term587 _69584 s).
Proof. exact (MK_COMB (@lem5307593) (@lem5307592 _69584 s)). Qed.
Lemma lem5307595 (b : real) (_69584 : real) : (real_le b _69584) = (real_le b _69584).
Proof. exact (eq_refl (real_le b _69584)). Qed.
Lemma lem5307596 (s : real -> Prop) (b : real) (_69584 : real) : (term584 s b _69584) = (term47 s b _69584).
Proof. exact (MK_COMB (@lem5307594 _69584 s) (@lem5307595 b _69584)). Qed.
Lemma lem5307597 (s : real -> Prop) (b : real) (_69584 : real) : (term580 b _69584 s) = (term47 s b _69584).
Proof. exact (TRANS (@lem5307589 s b _69584) (@lem5307596 s b _69584)). Qed.
Lemma lem5307600 (_69584 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term47 s b _69584.
Proof. exact (EQ_MP (@lem5307597 s b _69584) (@lem5307586 _69584 b l s c h1)). Qed.
Lemma lem5307601 (x : type1019) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term588 x s c b.
Proof. exact (@lem5307600 (x s c b) b l s c h1). Qed.
Lemma lem5307604 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (@lem5307601 x b l s c h3 (@lem5307557 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307605 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term590 x s c b.
Proof. exact (fun h0 : term491 x s c b => @lem5307604 x x' b l s c h1 h2 h3). Qed.
Lemma lem5307607 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307608 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term590 x s c b) = (term589 x s c b).
Proof. exact (@lem5307607 (term589 x s c b)). Qed.
Lemma lem5307609 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (EQ_MP (@lem5307608 x s c b) (@lem5307605 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307611 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307166 b l s c h1) (@lem5307043 b l s c h1)). Qed.
Lemma lem5307612 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 s c.
Proof. exact (fun h0 : term206 s c => @lem5307611 b l s c h1). Qed.
Lemma lem5307614 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307615 (s : real -> Prop) (c : real) : (term548 s c) = (term46 s c).
Proof. exact (@lem5307614 (term46 s c)). Qed.
Lemma lem5307616 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307615 s c) (@lem5307612 b l s c h1)). Qed.
Lemma lem5307644 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5307645 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term552 x' _69581 _69580) = (term553 x' _69580 _69581).
Proof. exact (@lem5307644 (term499 x' _69581 _69580) (term206 _69580 _69581)). Qed.
Lemma lem5307651 (x : type1019) (_69580 : real -> Prop) (_69581 : real) (_69582 : real) : (term591 x _69580 _69581 _69582) = (term591 x _69580 _69581 _69582).
Proof. exact (eq_refl (term591 x _69580 _69581 _69582)). Qed.
Lemma lem5307652 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term539 x _69582 x' _69581 _69580) = (term592 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307651 x _69580 _69581 _69582) (@lem5307645 x' _69580 _69581)). Qed.
Lemma lem5307656 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5307657 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term592 x _69582 x' _69580 _69581) = (term593 x' x _69582 _69580 _69581).
Proof. exact (@lem5307656 (term499 x' _69581 _69580) (term491 x _69580 _69581 _69582) (term206 _69580 _69581)). Qed.
Lemma lem5307673 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term539 x _69582 x' _69581 _69580) = (term593 x' x _69582 _69580 _69581).
Proof. exact (TRANS (@lem5307652 x _69582 x' _69580 _69581) (@lem5307657 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307674 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307675 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term540 x _69582 x' _69581 _69580) = (term594 x' x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5307674 _69580) (@lem5307673 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307686 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5307687 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term595 x _69582 x' _69581 _69580) = (term596 x' x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5307686) (@lem5307675 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307691 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5307692 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term597 x' x _69582 _69580 _69581) = (term594 x' x _69582 _69580 _69581).
Proof. exact (@lem5307691 (_69580 = (@EMPTY real)) (term499 x' _69581 _69580) (term495 x _69582 _69580 _69581)). Qed.
Lemma lem5307720 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : ((term540 x _69582 x' _69581 _69580) = (term597 x' x _69582 _69580 _69581)) = ((term594 x' x _69582 _69580 _69581) = (term594 x' x _69582 _69580 _69581)).
Proof. exact (MK_COMB (@lem5307687 x' x _69582 _69580 _69581) (@lem5307692 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307722 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5307723 (x : Prop) : (x = x) = True.
Proof. exact (@lem5307722 Prop x). Qed.
Lemma lem5307724 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : ((term594 x' x _69582 _69580 _69581) = (term594 x' x _69582 _69580 _69581)) = True.
Proof. exact (@lem5307723 (term594 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307725 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : ((term540 x _69582 x' _69581 _69580) = (term597 x' x _69582 _69580 _69581)) = True.
Proof. exact (TRANS (@lem5307720 x' x _69582 _69580 _69581) (@lem5307724 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307726 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : True = ((term540 x _69582 x' _69581 _69580) = (term597 x' x _69582 _69580 _69581)).
Proof. exact (SYM (@lem5307725 x' x _69582 _69580 _69581)). Qed.
Lemma lem5307727 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term540 x _69582 x' _69581 _69580) = (term597 x' x _69582 _69580 _69581).
Proof. exact (EQ_MP (@lem5307726 x' x _69582 _69580 _69581) (@lem0)). Qed.
Lemma lem5307728 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term597 x' x _69582 _69580 _69581.
Proof. exact (EQ_MP (@lem5307727 x' x _69582 _69580 _69581) (@lem5307251 _69582 _69581 _69580 x x' h1)). Qed.
Lemma lem5307730 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5307731 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term597 x' x _69582 _69580 _69581) = (term598 x _69582 x' _69581 _69580).
Proof. exact (@lem5307730 (term504 x _69582 _69580 _69581) (term499 x' _69581 _69580)). Qed.
Lemma lem5307733 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5307734 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term599 x _69582 _69580 _69581) = (term600 x _69582 _69580 _69581).
Proof. exact (@lem5307733 (_69580 = (@EMPTY real)) (term495 x _69582 _69580 _69581)). Qed.
Lemma lem5307736 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5307737 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term601 x _69582 _69580 _69581) = (term602 x _69582 _69580 _69581).
Proof. exact (@lem5307736 (term491 x _69580 _69581 _69582) (term206 _69580 _69581)). Qed.
Lemma lem5307739 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5307740 (x : type1019) (_69580 : real -> Prop) (_69581 : real) (_69582 : real) : (term603 x _69580 _69581 _69582) = (term589 x _69580 _69581 _69582).
Proof. exact (@lem5307739 (term589 x _69580 _69581 _69582)). Qed.
Lemma lem5307741 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5307742 (x : type1019) (_69580 : real -> Prop) (_69581 : real) (_69582 : real) : (term604 x _69580 _69581 _69582) = (term605 x _69580 _69581 _69582).
Proof. exact (MK_COMB (@lem5307741) (@lem5307740 x _69580 _69581 _69582)). Qed.
Lemma lem5307744 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5307745 (_69580 : real -> Prop) (_69581 : real) : (term570 _69580 _69581) = (term46 _69580 _69581).
Proof. exact (@lem5307744 (term46 _69580 _69581)). Qed.
Lemma lem5307746 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term602 x _69582 _69580 _69581) = (term606 x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5307742 x _69580 _69581 _69582) (@lem5307745 _69580 _69581)). Qed.
Lemma lem5307747 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term601 x _69582 _69580 _69581) = (term606 x _69582 _69580 _69581).
Proof. exact (TRANS (@lem5307737 x _69582 _69580 _69581) (@lem5307746 x _69582 _69580 _69581)). Qed.
Lemma lem5307748 (_69580 : real -> Prop) : (term54 _69580) = (term54 _69580).
Proof. exact (eq_refl (term54 _69580)). Qed.
Lemma lem5307749 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term600 x _69582 _69580 _69581) = (term607 x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5307748 _69580) (@lem5307747 x _69582 _69580 _69581)). Qed.
Lemma lem5307750 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term599 x _69582 _69580 _69581) = (term607 x _69582 _69580 _69581).
Proof. exact (TRANS (@lem5307734 x _69582 _69580 _69581) (@lem5307749 x _69582 _69580 _69581)). Qed.
Lemma lem5307751 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5307752 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term608 x _69582 _69580 _69581) = (term609 x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5307751) (@lem5307750 x _69582 _69580 _69581)). Qed.
Lemma lem5307753 (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term499 x' _69581 _69580) = (term499 x' _69581 _69580).
Proof. exact (eq_refl (term499 x' _69581 _69580)). Qed.
Lemma lem5307754 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term598 x _69582 x' _69581 _69580) = (term610 x _69582 x' _69581 _69580).
Proof. exact (MK_COMB (@lem5307752 x _69582 _69580 _69581) (@lem5307753 x' _69581 _69580)). Qed.
Lemma lem5307755 (x : type1019) (_69582 : real) (x' : type1021) (_69581 : real) (_69580 : real -> Prop) : (term597 x' x _69582 _69580 _69581) = (term610 x _69582 x' _69581 _69580).
Proof. exact (TRANS (@lem5307731 x _69582 x' _69581 _69580) (@lem5307754 x _69582 x' _69581 _69580)). Qed.
Lemma lem5307757 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term606 x b s c.
Proof. exact (conj (@lem5307609 x x' b l s c h1 h2 h3) (@lem5307616 b l s c h3)). Qed.
Lemma lem5307758 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term607 x b s c.
Proof. exact (conj (@lem5307364 b l s c h3) (@lem5307757 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307760 (_69582 : real) (_69581 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term610 x _69582 x' _69581 _69580.
Proof. exact (EQ_MP (@lem5307755 x _69582 x' _69581 _69580) (@lem5307728 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307761 (b : real) (c : real) (s : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term610 x b x' c s.
Proof. exact (@lem5307760 b c s x x' h1). Qed.
Lemma lem5307764 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term550 x' c s) (h3 : term179 b l s c) : term499 x' c s.
Proof. exact (@lem5307761 b c s x x' h1 (@lem5307758 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307765 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term611 x' c s.
Proof. exact (fun h0 : term550 x' c s => @lem5307764 x x' b l s c h1 h0 h2). Qed.
Lemma lem5307767 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307768 (x' : type1021) (c : real) (s : real -> Prop) : (term611 x' c s) = (term499 x' c s).
Proof. exact (@lem5307767 (term499 x' c s)). Qed.
Lemma lem5307769 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term499 x' c s.
Proof. exact (EQ_MP (@lem5307768 x' c s) (@lem5307765 x x' b l s c h1 h2)). Qed.
Lemma lem5307771 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5306822 b l s c h1)). Qed.
Lemma lem5307772 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5307771 b l s c h1). Qed.
Lemma lem5307774 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5307775 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5307774 (s = (@EMPTY real))). Qed.
Lemma lem5307776 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5307775 s) (@lem5307772 b l s c h1)). Qed.
Lemma lem5307778 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (proj1 (@lem5306822 b l s c h1)). Qed.
Lemma lem5307779 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term546 s.
Proof. exact (fun h0 : s = (@EMPTY real) => @lem5307778 b l s c h1). Qed.
Lemma lem5307781 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5307782 (s : real -> Prop) : (term546 s) = (term138 s).
Proof. exact (@lem5307781 (s = (@EMPTY real))). Qed.
Lemma lem5307783 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term138 s.
Proof. exact (EQ_MP (@lem5307782 s) (@lem5307779 b l s c h1)). Qed.
Lemma lem5307785 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307166 b l s c h1) (@lem5307043 b l s c h1)). Qed.
Lemma lem5307786 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 s c.
Proof. exact (fun h0 : term206 s c => @lem5307785 b l s c h1). Qed.
Lemma lem5307788 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307789 (s : real -> Prop) (c : real) : (term548 s c) = (term46 s c).
Proof. exact (@lem5307788 (term46 s c)). Qed.
Lemma lem5307790 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307789 s c) (@lem5307786 b l s c h1)). Qed.
Lemma lem5307793 (x' : type1021) (s : real -> Prop) (c : real) (h1 : term612 x' s c) : term612 x' s c.
Proof. exact (h1). Qed.
Lemma lem5307794 (x' : type1021) (s : real -> Prop) (c : real) (h1 : term612 x' s c) : term613 x' s c.
Proof. exact (fun h0 : term500 x' s c => @lem5307793 x' s c h1). Qed.
Lemma lem5307796 (p : Prop) : (term547 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem5307797 (x' : type1021) (s : real -> Prop) (c : real) : (term613 x' s c) = (term612 x' s c).
Proof. exact (@lem5307796 (term500 x' s c)). Qed.
Lemma lem5307798 (x' : type1021) (s : real -> Prop) (c : real) (h1 : term612 x' s c) : term612 x' s c.
Proof. exact (EQ_MP (@lem5307797 x' s c) (@lem5307794 x' s c h1)). Qed.
Lemma lem5307826 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5307827 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term614 x' _69580 _69581) = (term615 x' _69580 _69581).
Proof. exact (@lem5307826 (term500 x' _69580 _69581) (term206 _69580 _69581)). Qed.
Lemma lem5307833 (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term554 x _69581 _69582 _69580) = (term554 x _69581 _69582 _69580).
Proof. exact (eq_refl (term554 x _69581 _69582 _69580)). Qed.
Lemma lem5307834 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term527 x _69582 x' _69580 _69581) = (term616 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307833 x _69581 _69582 _69580) (@lem5307827 x' _69580 _69581)). Qed.
Lemma lem5307845 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307846 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term528 x _69582 x' _69580 _69581) = (term617 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307845 _69580) (@lem5307834 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5307858 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term618 x _69582 x' _69580 _69581) = (term619 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307857) (@lem5307846 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307862 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5307863 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term620 x _69582 x' _69580 _69581) = (term528 x _69582 x' _69580 _69581).
Proof. exact (@lem5307862 (_69580 = (@EMPTY real)) (term490 x _69581 _69582 _69580) (term614 x' _69580 _69581)). Qed.
Lemma lem5307889 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5307890 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term614 x' _69580 _69581) = (term615 x' _69580 _69581).
Proof. exact (@lem5307889 (term500 x' _69580 _69581) (term206 _69580 _69581)). Qed.
Lemma lem5307896 (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term554 x _69581 _69582 _69580) = (term554 x _69581 _69582 _69580).
Proof. exact (eq_refl (term554 x _69581 _69582 _69580)). Qed.
Lemma lem5307897 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term527 x _69582 x' _69580 _69581) = (term616 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307896 x _69581 _69582 _69580) (@lem5307890 x' _69580 _69581)). Qed.
Lemma lem5307908 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5307909 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term528 x _69582 x' _69580 _69581) = (term617 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307908 _69580) (@lem5307897 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307920 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term620 x _69582 x' _69580 _69581) = (term617 x _69582 x' _69580 _69581).
Proof. exact (TRANS (@lem5307863 x _69582 x' _69580 _69581) (@lem5307909 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307921 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : ((term528 x _69582 x' _69580 _69581) = (term620 x _69582 x' _69580 _69581)) = ((term617 x _69582 x' _69580 _69581) = (term617 x _69582 x' _69580 _69581)).
Proof. exact (MK_COMB (@lem5307858 x _69582 x' _69580 _69581) (@lem5307920 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307923 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5307924 (x : Prop) : (x = x) = True.
Proof. exact (@lem5307923 Prop x). Qed.
Lemma lem5307925 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : ((term617 x _69582 x' _69580 _69581) = (term617 x _69582 x' _69580 _69581)) = True.
Proof. exact (@lem5307924 (term617 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307926 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : ((term528 x _69582 x' _69580 _69581) = (term620 x _69582 x' _69580 _69581)) = True.
Proof. exact (TRANS (@lem5307921 x _69582 x' _69580 _69581) (@lem5307925 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307927 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : True = ((term528 x _69582 x' _69580 _69581) = (term620 x _69582 x' _69580 _69581)).
Proof. exact (SYM (@lem5307926 x _69582 x' _69580 _69581)). Qed.
Lemma lem5307928 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term528 x _69582 x' _69580 _69581) = (term620 x _69582 x' _69580 _69581).
Proof. exact (EQ_MP (@lem5307927 x _69582 x' _69580 _69581) (@lem0)). Qed.
Lemma lem5307929 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term620 x _69582 x' _69580 _69581.
Proof. exact (EQ_MP (@lem5307928 x _69582 x' _69580 _69581) (@lem5307209 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307931 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5307932 (x' : type1021) (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term620 x _69582 x' _69580 _69581) = (term621 x' x _69581 _69582 _69580).
Proof. exact (@lem5307931 (term622 x' _69580 _69581) (term490 x _69581 _69582 _69580)). Qed.
Lemma lem5307934 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5307935 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term623 x' _69580 _69581) = (term624 x' _69580 _69581).
Proof. exact (@lem5307934 (_69580 = (@EMPTY real)) (term614 x' _69580 _69581)). Qed.
Lemma lem5307937 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5307938 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term625 x' _69580 _69581) = (term626 x' _69580 _69581).
Proof. exact (@lem5307937 (term206 _69580 _69581) (term500 x' _69580 _69581)). Qed.
Lemma lem5307940 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5307941 (_69580 : real -> Prop) (_69581 : real) : (term570 _69580 _69581) = (term46 _69580 _69581).
Proof. exact (@lem5307940 (term46 _69580 _69581)). Qed.
Lemma lem5307942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5307943 (_69580 : real -> Prop) (_69581 : real) : (term571 _69580 _69581) = (term572 _69580 _69581).
Proof. exact (MK_COMB (@lem5307942) (@lem5307941 _69580 _69581)). Qed.
Lemma lem5307944 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term612 x' _69580 _69581) = (term612 x' _69580 _69581).
Proof. exact (eq_refl (term612 x' _69580 _69581)). Qed.
Lemma lem5307945 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term626 x' _69580 _69581) = (term627 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307943 _69580 _69581) (@lem5307944 x' _69580 _69581)). Qed.
Lemma lem5307946 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term625 x' _69580 _69581) = (term627 x' _69580 _69581).
Proof. exact (TRANS (@lem5307938 x' _69580 _69581) (@lem5307945 x' _69580 _69581)). Qed.
Lemma lem5307947 (_69580 : real -> Prop) : (term54 _69580) = (term54 _69580).
Proof. exact (eq_refl (term54 _69580)). Qed.
Lemma lem5307948 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term624 x' _69580 _69581) = (term628 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307947 _69580) (@lem5307946 x' _69580 _69581)). Qed.
Lemma lem5307949 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term623 x' _69580 _69581) = (term628 x' _69580 _69581).
Proof. exact (TRANS (@lem5307935 x' _69580 _69581) (@lem5307948 x' _69580 _69581)). Qed.
Lemma lem5307950 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5307951 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term629 x' _69580 _69581) = (term630 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5307950) (@lem5307949 x' _69580 _69581)). Qed.
Lemma lem5307952 (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term490 x _69581 _69582 _69580) = (term490 x _69581 _69582 _69580).
Proof. exact (eq_refl (term490 x _69581 _69582 _69580)). Qed.
Lemma lem5307953 (x' : type1021) (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term621 x' x _69581 _69582 _69580) = (term631 x' x _69581 _69582 _69580).
Proof. exact (MK_COMB (@lem5307951 x' _69580 _69581) (@lem5307952 x _69581 _69582 _69580)). Qed.
Lemma lem5307954 (x' : type1021) (x : type1019) (_69581 : real) (_69582 : real) (_69580 : real -> Prop) : (term620 x _69582 x' _69580 _69581) = (term631 x' x _69581 _69582 _69580).
Proof. exact (TRANS (@lem5307932 x' x _69581 _69582 _69580) (@lem5307953 x' x _69581 _69582 _69580)). Qed.
Lemma lem5307956 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term612 x' s c) (h2 : term179 b l s c) : term627 x' s c.
Proof. exact (conj (@lem5307790 b l s c h2) (@lem5307798 x' s c h1)). Qed.
Lemma lem5307957 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term612 x' s c) (h2 : term179 b l s c) : term628 x' s c.
Proof. exact (conj (@lem5307783 b l s c h2) (@lem5307956 x' b l s c h1 h2)). Qed.
Lemma lem5307959 (_69581 : real) (_69582 : real) (_69580 : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term631 x' x _69581 _69582 _69580.
Proof. exact (EQ_MP (@lem5307954 x' x _69581 _69582 _69580) (@lem5307929 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5307960 (c : real) (_69582 : real) (s : real -> Prop) (x : type1019) (x' : type1021) (h1 : term416 x x') : term631 x' x c _69582 s.
Proof. exact (@lem5307959 c _69582 s x x' h1). Qed.
Lemma lem5307963 (_69582 : real) (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term490 x c _69582 s.
Proof. exact (@lem5307960 c _69582 s x x' h1 (@lem5307957 x' b l s c h2 h3)). Qed.
Lemma lem5307964 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (@lem5307963 b x x' b l s c h1 h2 h3). Qed.
Lemma lem5307965 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term578 x c b s.
Proof. exact (fun h0 : term579 x c b s => @lem5307964 x x' b l s c h1 h2 h3). Qed.
Lemma lem5307967 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307968 (x : type1019) (c : real) (b : real) (s : real -> Prop) : (term578 x c b s) = (term490 x c b s).
Proof. exact (@lem5307967 (term490 x c b s)). Qed.
Lemma lem5307969 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term490 x c b s.
Proof. exact (EQ_MP (@lem5307968 x c b s) (@lem5307965 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307971 (_69584 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term47 s b _69584.
Proof. exact (EQ_MP (@lem5307597 s b _69584) (@lem5307586 _69584 b l s c h1)). Qed.
Lemma lem5307972 (x : type1019) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term588 x s c b.
Proof. exact (@lem5307971 (x s c b) b l s c h1). Qed.
Lemma lem5307975 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (@lem5307972 x b l s c h3 (@lem5307969 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307976 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term590 x s c b.
Proof. exact (fun h0 : term491 x s c b => @lem5307975 x x' b l s c h1 h2 h3). Qed.
Lemma lem5307978 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307979 (x : type1019) (s : real -> Prop) (c : real) (b : real) : (term590 x s c b) = (term589 x s c b).
Proof. exact (@lem5307978 (term589 x s c b)). Qed.
Lemma lem5307980 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term589 x s c b.
Proof. exact (EQ_MP (@lem5307979 x s c b) (@lem5307976 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5307982 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307166 b l s c h1) (@lem5307043 b l s c h1)). Qed.
Lemma lem5307983 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term548 s c.
Proof. exact (fun h0 : term206 s c => @lem5307982 b l s c h1). Qed.
Lemma lem5307985 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5307986 (s : real -> Prop) (c : real) : (term548 s c) = (term46 s c).
Proof. exact (@lem5307985 (term46 s c)). Qed.
Lemma lem5307987 (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term46 s c.
Proof. exact (EQ_MP (@lem5307986 s c) (@lem5307983 b l s c h1)). Qed.
Lemma lem5308015 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5308016 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term614 x' _69580 _69581) = (term615 x' _69580 _69581).
Proof. exact (@lem5308015 (term500 x' _69580 _69581) (term206 _69580 _69581)). Qed.
Lemma lem5308022 (x : type1019) (_69580 : real -> Prop) (_69581 : real) (_69582 : real) : (term591 x _69580 _69581 _69582) = (term591 x _69580 _69581 _69582).
Proof. exact (eq_refl (term591 x _69580 _69581 _69582)). Qed.
Lemma lem5308023 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term531 x _69582 x' _69580 _69581) = (term632 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5308022 x _69580 _69581 _69582) (@lem5308016 x' _69580 _69581)). Qed.
Lemma lem5308027 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5308028 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term632 x _69582 x' _69580 _69581) = (term633 x' x _69582 _69580 _69581).
Proof. exact (@lem5308027 (term500 x' _69580 _69581) (term491 x _69580 _69581 _69582) (term206 _69580 _69581)). Qed.
Lemma lem5308044 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term531 x _69582 x' _69580 _69581) = (term633 x' x _69582 _69580 _69581).
Proof. exact (TRANS (@lem5308023 x _69582 x' _69580 _69581) (@lem5308028 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308045 (_69580 : real -> Prop) : (term213 _69580) = (term213 _69580).
Proof. exact (eq_refl (term213 _69580)). Qed.
Lemma lem5308046 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term532 x _69582 x' _69580 _69581) = (term634 x' x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5308045 _69580) (@lem5308044 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308057 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5308058 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term635 x _69582 x' _69580 _69581) = (term636 x' x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5308057) (@lem5308046 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308062 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem5308063 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term637 x' x _69582 _69580 _69581) = (term634 x' x _69582 _69580 _69581).
Proof. exact (@lem5308062 (_69580 = (@EMPTY real)) (term500 x' _69580 _69581) (term495 x _69582 _69580 _69581)). Qed.
Lemma lem5308091 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : ((term532 x _69582 x' _69580 _69581) = (term637 x' x _69582 _69580 _69581)) = ((term634 x' x _69582 _69580 _69581) = (term634 x' x _69582 _69580 _69581)).
Proof. exact (MK_COMB (@lem5308058 x' x _69582 _69580 _69581) (@lem5308063 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308093 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5308094 (x : Prop) : (x = x) = True.
Proof. exact (@lem5308093 Prop x). Qed.
Lemma lem5308095 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : ((term634 x' x _69582 _69580 _69581) = (term634 x' x _69582 _69580 _69581)) = True.
Proof. exact (@lem5308094 (term634 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308096 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : ((term532 x _69582 x' _69580 _69581) = (term637 x' x _69582 _69580 _69581)) = True.
Proof. exact (TRANS (@lem5308091 x' x _69582 _69580 _69581) (@lem5308095 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308097 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : True = ((term532 x _69582 x' _69580 _69581) = (term637 x' x _69582 _69580 _69581)).
Proof. exact (SYM (@lem5308096 x' x _69582 _69580 _69581)). Qed.
Lemma lem5308098 (x' : type1021) (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term532 x _69582 x' _69580 _69581) = (term637 x' x _69582 _69580 _69581).
Proof. exact (EQ_MP (@lem5308097 x' x _69582 _69580 _69581) (@lem0)). Qed.
Lemma lem5308099 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term637 x' x _69582 _69580 _69581.
Proof. exact (EQ_MP (@lem5308098 x' x _69582 _69580 _69581) (@lem5307223 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5308101 (b : Prop) (a : Prop) : (a \/ b) = (term560 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5308102 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term637 x' x _69582 _69580 _69581) = (term638 x _69582 x' _69580 _69581).
Proof. exact (@lem5308101 (term504 x _69582 _69580 _69581) (term500 x' _69580 _69581)). Qed.
Lemma lem5308104 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5308105 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term599 x _69582 _69580 _69581) = (term600 x _69582 _69580 _69581).
Proof. exact (@lem5308104 (_69580 = (@EMPTY real)) (term495 x _69582 _69580 _69581)). Qed.
Lemma lem5308107 (a : Prop) (b : Prop) : (term563 a b) = (term564 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem5308108 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term601 x _69582 _69580 _69581) = (term602 x _69582 _69580 _69581).
Proof. exact (@lem5308107 (term491 x _69580 _69581 _69582) (term206 _69580 _69581)). Qed.
Lemma lem5308110 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5308111 (x : type1019) (_69580 : real -> Prop) (_69581 : real) (_69582 : real) : (term603 x _69580 _69581 _69582) = (term589 x _69580 _69581 _69582).
Proof. exact (@lem5308110 (term589 x _69580 _69581 _69582)). Qed.
Lemma lem5308112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5308113 (x : type1019) (_69580 : real -> Prop) (_69581 : real) (_69582 : real) : (term604 x _69580 _69581 _69582) = (term605 x _69580 _69581 _69582).
Proof. exact (MK_COMB (@lem5308112) (@lem5308111 x _69580 _69581 _69582)). Qed.
Lemma lem5308115 (a : Prop) : (term569 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5308116 (_69580 : real -> Prop) (_69581 : real) : (term570 _69580 _69581) = (term46 _69580 _69581).
Proof. exact (@lem5308115 (term46 _69580 _69581)). Qed.
Lemma lem5308117 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term602 x _69582 _69580 _69581) = (term606 x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5308113 x _69580 _69581 _69582) (@lem5308116 _69580 _69581)). Qed.
Lemma lem5308118 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term601 x _69582 _69580 _69581) = (term606 x _69582 _69580 _69581).
Proof. exact (TRANS (@lem5308108 x _69582 _69580 _69581) (@lem5308117 x _69582 _69580 _69581)). Qed.
Lemma lem5308119 (_69580 : real -> Prop) : (term54 _69580) = (term54 _69580).
Proof. exact (eq_refl (term54 _69580)). Qed.
Lemma lem5308120 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term600 x _69582 _69580 _69581) = (term607 x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5308119 _69580) (@lem5308118 x _69582 _69580 _69581)). Qed.
Lemma lem5308121 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term599 x _69582 _69580 _69581) = (term607 x _69582 _69580 _69581).
Proof. exact (TRANS (@lem5308105 x _69582 _69580 _69581) (@lem5308120 x _69582 _69580 _69581)). Qed.
Lemma lem5308122 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5308123 (x : type1019) (_69582 : real) (_69580 : real -> Prop) (_69581 : real) : (term608 x _69582 _69580 _69581) = (term609 x _69582 _69580 _69581).
Proof. exact (MK_COMB (@lem5308122) (@lem5308121 x _69582 _69580 _69581)). Qed.
Lemma lem5308124 (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term500 x' _69580 _69581) = (term500 x' _69580 _69581).
Proof. exact (eq_refl (term500 x' _69580 _69581)). Qed.
Lemma lem5308125 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term638 x _69582 x' _69580 _69581) = (term639 x _69582 x' _69580 _69581).
Proof. exact (MK_COMB (@lem5308123 x _69582 _69580 _69581) (@lem5308124 x' _69580 _69581)). Qed.
Lemma lem5308126 (x : type1019) (_69582 : real) (x' : type1021) (_69580 : real -> Prop) (_69581 : real) : (term637 x' x _69582 _69580 _69581) = (term639 x _69582 x' _69580 _69581).
Proof. exact (TRANS (@lem5308102 x _69582 x' _69580 _69581) (@lem5308125 x _69582 x' _69580 _69581)). Qed.
Lemma lem5308128 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term606 x b s c.
Proof. exact (conj (@lem5307980 x x' b l s c h1 h2 h3) (@lem5307987 b l s c h3)). Qed.
Lemma lem5308129 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term607 x b s c.
Proof. exact (conj (@lem5307776 b l s c h3) (@lem5308128 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5308131 (_69582 : real) (_69580 : real -> Prop) (_69581 : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term639 x _69582 x' _69580 _69581.
Proof. exact (EQ_MP (@lem5308126 x _69582 x' _69580 _69581) (@lem5308099 _69582 _69580 _69581 x x' h1)). Qed.
Lemma lem5308132 (b : real) (s : real -> Prop) (c : real) (x : type1019) (x' : type1021) (h1 : term416 x x') : term639 x b x' s c.
Proof. exact (@lem5308131 b s c x x' h1). Qed.
Lemma lem5308135 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term612 x' s c) (h3 : term179 b l s c) : term500 x' s c.
Proof. exact (@lem5308132 b s c x x' h1 (@lem5308129 x x' b l s c h1 h2 h3)). Qed.
Lemma lem5308136 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term640 x' s c.
Proof. exact (fun h0 : term612 x' s c => @lem5308135 x x' b l s c h1 h0 h2). Qed.
Lemma lem5308138 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5308139 (x' : type1021) (s : real -> Prop) (c : real) : (term640 x' s c) = (term500 x' s c).
Proof. exact (@lem5308138 (term500 x' s c)). Qed.
Lemma lem5308140 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term500 x' s c.
Proof. exact (EQ_MP (@lem5308139 x' s c) (@lem5308136 x x' b l s c h1 h2)). Qed.
Lemma lem5308142 (a : Prop) (b : Prop) : (term641 a b) = (term642 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem5308143 (s : real -> Prop) (_69583 : real) (c : real) : (term73 s _69583 c) = (term72 s _69583 c).
Proof. exact (@lem5308142 (@IN real _69583 s) (real_lt _69583 c)). Qed.
Lemma lem5308145 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5308146 (s : real -> Prop) (_69583 : real) (c : real) : (term72 s _69583 c) = (term643 s _69583 c).
Proof. exact (@lem5308145 (term44 s _69583 c)). Qed.
Lemma lem5308147 (s : real -> Prop) (_69583 : real) (c : real) : (term73 s _69583 c) = (term643 s _69583 c).
Proof. exact (TRANS (@lem5308143 s _69583 c) (@lem5308146 s _69583 c)). Qed.
Lemma lem5308149 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term422 x' s c.
Proof. exact (conj (@lem5307769 x x' b l s c h1 h2) (@lem5308140 x x' b l s c h1 h2)). Qed.
Lemma lem5308151 (_69583 : real) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term643 s _69583 c.
Proof. exact (EQ_MP (@lem5308147 s _69583 c) (@lem5307154 _69583 b l s c h1)). Qed.
Lemma lem5308152 (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term179 b l s c) : term644 x' s c.
Proof. exact (@lem5308151 (x' s c) b l s c h1). Qed.
Lemma lem5308155 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (@lem5308152 x' b l s c h2 (@lem5308149 x x' b l s c h1 h2)). Qed.
Lemma lem5308156 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : term645.
Proof. exact (fun h0 : ~ False => @lem5308155 x x' b l s c h1 h2). Qed.
Lemma lem5308158 (p : Prop) : (term549 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5308159 : term645 = False.
Proof. exact (@lem5308158 False). Qed.
Lemma lem5308161 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (EQ_MP (@lem5308159) (@lem5308156 x x' b l s c h1 h2)). Qed.
Lemma lem5308162 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : (term179 b l s c) = False.
Proof. exact (prop_ext (fun h3 : term179 b l s c => @lem5308161 x x' b l s c h1 h2) (fun h3 : False => @lem5306818 b l s c h2)). Qed.
Lemma lem5308163 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (EQ_MP (@lem5308162 x x' b l s c h1 h2) (@lem5306818 b l s c h2)). Qed.
Lemma lem5308164 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : (term416 x x') = False.
Proof. exact (prop_ext (fun h3 : term416 x x' => @lem5308163 x x' b l s c h1 h2) (fun h3 : False => @lem5306748 x x' h1)). Qed.
Lemma lem5308165 (x : type1019) (x' : type1021) (b : real) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term179 b l s c) : False.
Proof. exact (EQ_MP (@lem5308164 x x' b l s c h1 h2) (@lem5306748 x x' h1)). Qed.
Lemma lem5308166 (x : type1019) (x' : type1021) (l : real) (s : real -> Prop) (c : real) (h1 : term416 x x') (h2 : term182 l s c) : False.
Proof. exact (ex_elim (@lem5306666 l s c h2) (fun b : real => fun h0 : term181 l s c b => @lem5308165 x x' b l s c h1 h0)). Qed.
Lemma lem5308167 (x : type1019) (x' : type1021) (l : real) (s : real -> Prop) (h1 : term416 x x') (h2 : term184 l s) : False.
Proof. exact (ex_elim (@lem5306665 l s h2) (fun c : real => fun h0 : term183 l s c => @lem5308166 x x' l s c h1 h0)). Qed.
Lemma lem5308168 (x : type1019) (x' : type1021) (s : real -> Prop) (h1 : term416 x x') (h2 : term186 s) : False.
Proof. exact (ex_elim (@lem5306664 s h2) (fun l : real => fun h0 : term185 s l => @lem5308167 x x' l s h1 h0)). Qed.
Lemma lem5308169 (x : type1019) (x' : type1021) (h1 : term416 x x') (h2 : term34) : False.
Proof. exact (ex_elim (@lem5306172 h2) (fun s : real -> Prop => fun h0 : term187 s => @lem5308168 x x' s h1 h0)). Qed.
Lemma lem5308170 (x : type1019) (h1 : term419 x) (h2 : term34) : False.
Proof. exact (ex_elim (@lem5306662 x h1) (fun x' : type1021 => fun h0 : term418 x x' => @lem5308169 x x' h0 h2)). Qed.
Lemma lem5308171 (h1 : term41) (h2 : term34) : False.
Proof. exact (ex_elim (@lem5306661 h1) (fun x : type1019 => fun h0 : term420 x => @lem5308170 x h0 h2)). Qed.
Lemma lem5308172 (h1 : term34) : term39.
Proof. exact (fun h0 : term41 => @lem5308171 h0 h1). Qed.
Lemma lem5308173 : term39 = term40.
Proof. exact (@lem69 term41). Qed.
Lemma lem5308174 (h1 : term34) : term40.
Proof. exact (EQ_MP (@lem5308173) (@lem5308172 h1)). Qed.
Lemma lem5308175 : term43.
Proof. exact (fun h0 : term34 => @lem5308174 h0). Qed.
Lemma lem5308176 : term35.
Proof. exact (EQ_MP (@lem5305819) (@lem5308175)). Qed.
Lemma lem5308178 : term35.
Proof. exact (@lem5305468 (@lem5308176)). Qed.
Lemma lem5308179 (h1 : term34) : term39.
Proof. exact (@lem5308178 (@lem5305453 h1)). Qed.
Lemma lem5308180 (h1 : term34) : False.
Proof. exact (@lem5308179 h1 (@lem5285051)). Qed.
Lemma lem5308181 (h1 : term34) : term34 = False.
Proof. exact (prop_ext (fun h2 : term34 => @lem5308180 h1) (fun h2 : False => @lem5305453 h1)). Qed.
Lemma lem5308182 (h1 : term34) : False.
Proof. exact (EQ_MP (@lem5308181 h1) (@lem5305453 h1)). Qed.
Lemma lem5308183 : term33.
Proof. exact (fun h0 : term34 => @lem5308182 h0). Qed.
Lemma lem5308184 : term31.
Proof. exact (EQ_MP (@lem5305452) (@lem5308183)). Qed.
Lemma lem5308185 : term30.
Proof. exact (EQ_MP (@lem5305448) (@lem5308184)). Qed.
