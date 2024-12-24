Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REP_ABS_PAIR_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm44425_spec.
Require Import thm44434_spec.
Require Import thm69_spec.
Lemma lem44435 {A B : Type'} : term0 A B.
Proof. exact (fun r : type1413 A B => @lem44434 A B r). Qed.
Lemma lem44436 {A B : Type'} : term1 A B.
Proof. exact (fun a : prod A B => @lem44425 A B a). Qed.
Lemma lem44437 {A B : Type'} : term2 A B.
Proof. exact (conj (@lem44436 A B) (@lem44435 A B)). Qed.
Lemma lem44449 (p : Prop) : p = (term3 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem44450 {A B : Type'} : (term4 A B) = (term5 A B).
Proof. exact (@lem44449 (term4 A B)). Qed.
Lemma lem44451 {A B : Type'} : (term5 A B) = (term4 A B).
Proof. exact (SYM (@lem44450 A B)). Qed.
Lemma lem44452 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem44453 {A B : Type'} : term2 A B.
Proof. exact (@lem44437 A B). Qed.
Lemma lem44459 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem44460 {A B : Type'} : term8 A B.
Proof. exact (fun h0 : term7 A B => @lem44459 A B h0). Qed.
Lemma lem44461 {A B : Type'} (h1 : term8 A B) : term8 A B.
Proof. exact (h1). Qed.
Lemma lem44462 {A B : Type'} (h1 : term7 A B) : term7 A B.
Proof. exact (h1). Qed.
Lemma lem44463 {A B : Type'} (h1 : term7 A B) (h2 : term8 A B) : term7 A B.
Proof. exact (@lem44461 A B h2 (@lem44462 A B h1)). Qed.
Lemma lem44464 {A B : Type'} (h1 : term7 A B) : term9 A B.
Proof. exact (fun h0 : term8 A B => @lem44463 A B h1 h0). Qed.
Lemma lem44465 {A B : Type'} (h1 : term8 A B) : term8 A B.
Proof. exact (h1). Qed.
Lemma lem44466 {A B : Type'} (h1 : term7 A B) (h2 : term8 A B) : term7 A B.
Proof. exact (@lem44464 A B h1 (@lem44465 A B h2)). Qed.
Lemma lem44467 {A B : Type'} (h1 : term8 A B) : term8 A B.
Proof. exact (fun h0 : term7 A B => @lem44466 A B h0 h1). Qed.
Lemma lem44468 {A B : Type'} : term10 A B.
Proof. exact (fun h0 : term8 A B => @lem44467 A B h0). Qed.
Lemma lem44471 {A B : Type'} : term8 A B.
Proof. exact (@lem44468 A B (@lem44460 A B)). Qed.
Lemma lem44472 {A B : Type'} : term8 A B.
Proof. exact (@lem44471 A B). Qed.
Lemma lem44484 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem44485 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (@lem44484 (term2 A B)). Qed.
Lemma lem44504 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (eq_refl (term13 A B)). Qed.
Lemma lem44511 {A B : Type'} : (term7 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem44504 A B) (@lem44485 A B)). Qed.
Lemma lem44512 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem44513 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (r = (@mk_pair A B a b)) = (r = (@mk_pair A B a b)).
Proof. exact (eq_refl (r = (@mk_pair A B a b))). Qed.
Lemma lem44514 {A B : Type'} (r : type1413 A B) (a : A) : (term16 A B r a) = (term16 A B r a).
Proof. exact (fun_ext (fun b : B => @lem44513 A B r a b)). Qed.
Lemma lem44515 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44516 {A B : Type'} (r : type1413 A B) (a : A) : (term17 A B r a) = (term17 A B r a).
Proof. exact (MK_COMB (@lem44515 B) (@lem44514 A B r a)). Qed.
Lemma lem44517 {A B : Type'} (r : type1413 A B) : (term18 A B r) = (term18 A B r).
Proof. exact (fun_ext (fun a : A => @lem44516 A B r a)). Qed.
Lemma lem44518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44519 {A B : Type'} (r : type1413 A B) : (term19 A B r) = (term19 A B r).
Proof. exact (MK_COMB (@lem44518 A) (@lem44517 A B r)). Qed.
Lemma lem44520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44521 {A B : Type'} (r : type1413 A B) : (term20 A B r) = (term20 A B r).
Proof. exact (MK_COMB (@lem44520) (@lem44519 A B r)). Qed.
Lemma lem44522 {A B : Type'} (r : type1413 A B) : ((term19 A B r) = ((term15 A B r) = r)) = ((term19 A B r) = ((term15 A B r) = r)).
Proof. exact (MK_COMB (@lem44521 A B r) (@lem44512 A B r)). Qed.
Lemma lem44523 {A B : Type'} : (term21 A B) = (term21 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44522 A B r)). Qed.
Lemma lem44524 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44525 {A B : Type'} : (term0 A B) = (term0 A B).
Proof. exact (MK_COMB (@lem44524 A B) (@lem44523 A B)). Qed.
Lemma lem44526 {A B : Type'} (a : prod A B) : ((term22 A B a) = a) = ((term22 A B a) = a).
Proof. exact (eq_refl ((term22 A B a) = a)). Qed.
Lemma lem44527 {A B : Type'} : (term23 A B) = (term23 A B).
Proof. exact (fun_ext (fun a : prod A B => @lem44526 A B a)). Qed.
Lemma lem44528 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem44529 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem44528 A B) (@lem44527 A B)). Qed.
Lemma lem44530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44531 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem44530) (@lem44529 A B)). Qed.
Lemma lem44532 {A B : Type'} : (term2 A B) = (term2 A B).
Proof. exact (MK_COMB (@lem44531 A B) (@lem44525 A B)). Qed.
Lemma lem44533 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44534 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem44533) (@lem44532 A B)). Qed.
Lemma lem44535 {A B : Type'} (x : A) (y : B) : ((term25 A B x y) = (@mk_pair A B x y)) = ((term25 A B x y) = (@mk_pair A B x y)).
Proof. exact (eq_refl ((term25 A B x y) = (@mk_pair A B x y))). Qed.
Lemma lem44536 {A B : Type'} (x : A) : (term26 A B x) = (term26 A B x).
Proof. exact (fun_ext (fun y : B => @lem44535 A B x y)). Qed.
Lemma lem44537 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem44538 {A B : Type'} (x : A) : (term27 A B x) = (term27 A B x).
Proof. exact (MK_COMB (@lem44537 B) (@lem44536 A B x)). Qed.
Lemma lem44539 {A B : Type'} : (term28 A B) = (term28 A B).
Proof. exact (fun_ext (fun x : A => @lem44538 A B x)). Qed.
Lemma lem44540 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem44541 {A B : Type'} : (term4 A B) = (term4 A B).
Proof. exact (MK_COMB (@lem44540 A) (@lem44539 A B)). Qed.
Lemma lem44542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44543 {A B : Type'} : (term6 A B) = (term6 A B).
Proof. exact (MK_COMB (@lem44542) (@lem44541 A B)). Qed.
Lemma lem44544 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem44545 {A B : Type'} : (term13 A B) = (term13 A B).
Proof. exact (MK_COMB (@lem44544) (@lem44543 A B)). Qed.
Lemma lem44546 {A B : Type'} : (term14 A B) = (term14 A B).
Proof. exact (MK_COMB (@lem44545 A B) (@lem44534 A B)). Qed.
Lemma lem44589 {A B : Type'} : (term7 A B) = (term14 A B).
Proof. exact (TRANS (@lem44511 A B) (@lem44546 A B)). Qed.
Lemma lem44590 {A B : Type'} : (term14 A B) = (term7 A B).
Proof. exact (SYM (@lem44589 A B)). Qed.
Lemma lem44591 {A B : Type'} (h1 : term6 A B) : term6 A B.
Proof. exact (h1). Qed.
Lemma lem44592 {A B : Type'} (h1 : term2 A B) : term2 A B.
Proof. exact (h1). Qed.
Lemma lem44594 {B : Type'} (P : B -> Prop) : (term29 B P) = (term30 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem44595 {A B : Type'} (x : A) : (term31 A B x) = (term32 A B x).
Proof. exact (@lem44594 B (term26 A B x)). Qed.
Lemma lem44596 {A B : Type'} (x : A) (y : B) : (term33 A B x y) = ((term25 A B x y) = (@mk_pair A B x y)).
Proof. exact (eq_refl (term33 A B x y)). Qed.
Lemma lem44597 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44599 {A B : Type'} (x : A) (y : B) : (term34 A B x y) = (term35 A B x y).
Proof. exact (MK_COMB (@lem44597) (@lem44596 A B x y)). Qed.
Lemma lem44600 {A B : Type'} (x : A) : (term36 A B x) = (term37 A B x).
Proof. exact (fun_ext (fun y : B => @lem44599 A B x y)). Qed.
Lemma lem44601 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44602 {A B : Type'} (x : A) : (term32 A B x) = (term38 A B x).
Proof. exact (MK_COMB (@lem44601 B) (@lem44600 A B x)). Qed.
Lemma lem44603 {A B : Type'} (x : A) : (term31 A B x) = (term38 A B x).
Proof. exact (TRANS (@lem44595 A B x) (@lem44602 A B x)). Qed.
Lemma lem44604 {A : Type'} (P : A -> Prop) : (term29 A P) = (term30 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem44605 {A B : Type'} : (term6 A B) = (term39 A B).
Proof. exact (@lem44604 A (term28 A B)). Qed.
Lemma lem44606 {A B : Type'} (x : A) : (term40 A B x) = (term27 A B x).
Proof. exact (eq_refl (term40 A B x)). Qed.
Lemma lem44607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44608 {A B : Type'} (x : A) : (term41 A B x) = (term31 A B x).
Proof. exact (MK_COMB (@lem44607) (@lem44606 A B x)). Qed.
Lemma lem44609 {A B : Type'} (x : A) : (term41 A B x) = (term38 A B x).
Proof. exact (TRANS (@lem44608 A B x) (@lem44603 A B x)). Qed.
Lemma lem44610 {A B : Type'} : (term42 A B) = (term43 A B).
Proof. exact (fun_ext (fun x : A => @lem44609 A B x)). Qed.
Lemma lem44611 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44612 {A B : Type'} : (term39 A B) = (term44 A B).
Proof. exact (MK_COMB (@lem44611 A) (@lem44610 A B)). Qed.
Lemma lem44625 {A B : Type'} : (term6 A B) = (term44 A B).
Proof. exact (TRANS (@lem44605 A B) (@lem44612 A B)). Qed.
Lemma lem44626 {A B : Type'} (h1 : term6 A B) : term44 A B.
Proof. exact (EQ_MP (@lem44625 A B) (@lem44591 A B h1)). Qed.
Lemma lem44627 {A B : Type'} (a : prod A B) : ((term22 A B a) = a) = ((term22 A B a) = a).
Proof. exact (eq_refl ((term22 A B a) = a)). Qed.
Lemma lem44628 {A B : Type'} : (term23 A B) = (term23 A B).
Proof. exact (fun_ext (fun a : prod A B => @lem44627 A B a)). Qed.
Lemma lem44629 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem44630 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem44629 A B) (@lem44628 A B)). Qed.
Lemma lem44632 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (r = (@mk_pair A B a b)) = (r = (@mk_pair A B a b)).
Proof. exact (eq_refl (r = (@mk_pair A B a b))). Qed.
Lemma lem44633 {B : Type'} (P : B -> Prop) : (term45 B P) = (term46 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem44634 {A B : Type'} (r : type1413 A B) (a : A) : (term47 A B r a) = (term48 A B r a).
Proof. exact (@lem44633 B (term16 A B r a)). Qed.
Lemma lem44635 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term49 A B r a b) = (r = (@mk_pair A B a b)).
Proof. exact (eq_refl (term49 A B r a b)). Qed.
Lemma lem44636 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44638 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term50 A B r a b) = (term51 A B r a b).
Proof. exact (MK_COMB (@lem44636) (@lem44635 A B r a b)). Qed.
Lemma lem44639 {A B : Type'} (r : type1413 A B) (a : A) : (term52 A B r a) = (term53 A B r a).
Proof. exact (fun_ext (fun b : B => @lem44638 A B r a b)). Qed.
Lemma lem44640 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem44641 {A B : Type'} (r : type1413 A B) (a : A) : (term48 A B r a) = (term54 A B r a).
Proof. exact (MK_COMB (@lem44640 B) (@lem44639 A B r a)). Qed.
Lemma lem44642 {A B : Type'} (r : type1413 A B) (a : A) : (term47 A B r a) = (term54 A B r a).
Proof. exact (TRANS (@lem44634 A B r a) (@lem44641 A B r a)). Qed.
Lemma lem44643 {A B : Type'} (r : type1413 A B) (a : A) : (term16 A B r a) = (term16 A B r a).
Proof. exact (fun_ext (fun b : B => @lem44632 A B r a b)). Qed.
Lemma lem44644 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44645 {A B : Type'} (r : type1413 A B) (a : A) : (term17 A B r a) = (term17 A B r a).
Proof. exact (MK_COMB (@lem44644 B) (@lem44643 A B r a)). Qed.
Lemma lem44646 {A : Type'} (P : A -> Prop) : (term45 A P) = (term46 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem44647 {A B : Type'} (r : type1413 A B) : (term55 A B r) = (term56 A B r).
Proof. exact (@lem44646 A (term18 A B r)). Qed.
Lemma lem44648 {A B : Type'} (r : type1413 A B) (a : A) : (term57 A B r a) = (term17 A B r a).
Proof. exact (eq_refl (term57 A B r a)). Qed.
Lemma lem44649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem44650 {A B : Type'} (r : type1413 A B) (a : A) : (term58 A B r a) = (term47 A B r a).
Proof. exact (MK_COMB (@lem44649) (@lem44648 A B r a)). Qed.
Lemma lem44651 {A B : Type'} (r : type1413 A B) (a : A) : (term58 A B r a) = (term54 A B r a).
Proof. exact (TRANS (@lem44650 A B r a) (@lem44642 A B r a)). Qed.
Lemma lem44652 {A B : Type'} (r : type1413 A B) : (term59 A B r) = (term60 A B r).
Proof. exact (fun_ext (fun a : A => @lem44651 A B r a)). Qed.
Lemma lem44653 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem44654 {A B : Type'} (r : type1413 A B) : (term56 A B r) = (term61 A B r).
Proof. exact (MK_COMB (@lem44653 A) (@lem44652 A B r)). Qed.
Lemma lem44655 {A B : Type'} (r : type1413 A B) : (term55 A B r) = (term61 A B r).
Proof. exact (TRANS (@lem44647 A B r) (@lem44654 A B r)). Qed.
Lemma lem44656 {A B : Type'} (r : type1413 A B) : (term18 A B r) = (term18 A B r).
Proof. exact (fun_ext (fun a : A => @lem44645 A B r a)). Qed.
Lemma lem44657 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44658 {A B : Type'} (r : type1413 A B) : (term19 A B r) = (term19 A B r).
Proof. exact (MK_COMB (@lem44657 A) (@lem44656 A B r)). Qed.
Lemma lem44659 {A B : Type'} (r : type1413 A B) : (term62 A B r) = (term62 A B r).
Proof. exact (eq_refl (term62 A B r)). Qed.
Lemma lem44660 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem44661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem44662 {A B : Type'} (r : type1413 A B) : (term63 A B r) = (term64 A B r).
Proof. exact (MK_COMB (@lem44661) (@lem44655 A B r)). Qed.
Lemma lem44663 {A B : Type'} (r : type1413 A B) : (term65 A B r) = (term66 A B r).
Proof. exact (MK_COMB (@lem44662 A B r) (@lem44660 A B r)). Qed.
Lemma lem44664 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem44665 {A B : Type'} (r : type1413 A B) : (term67 A B r) = (term67 A B r).
Proof. exact (MK_COMB (@lem44664) (@lem44658 A B r)). Qed.
Lemma lem44666 {A B : Type'} (r : type1413 A B) : (term68 A B r) = (term68 A B r).
Proof. exact (MK_COMB (@lem44665 A B r) (@lem44659 A B r)). Qed.
Lemma lem44667 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44668 {A B : Type'} (r : type1413 A B) : (term69 A B r) = (term69 A B r).
Proof. exact (MK_COMB (@lem44667) (@lem44666 A B r)). Qed.
Lemma lem44669 {A B : Type'} (r : type1413 A B) : (term70 A B r) = (term71 A B r).
Proof. exact (MK_COMB (@lem44668 A B r) (@lem44663 A B r)). Qed.
Lemma lem44670 {A B : Type'} (r : type1413 A B) : ((term19 A B r) = ((term15 A B r) = r)) = (term70 A B r).
Proof. exact (@lem17784 (term19 A B r) ((term15 A B r) = r)). Qed.
Lemma lem44671 {A B : Type'} (r : type1413 A B) : ((term19 A B r) = ((term15 A B r) = r)) = (term71 A B r).
Proof. exact (TRANS (@lem44670 A B r) (@lem44669 A B r)). Qed.
Lemma lem44672 {A B : Type'} : (term21 A B) = (term72 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44671 A B r)). Qed.
Lemma lem44673 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44674 {A B : Type'} : (term0 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem44673 A B) (@lem44672 A B)). Qed.
Lemma lem44675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44676 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem44675) (@lem44630 A B)). Qed.
Lemma lem44677 {A B : Type'} : (term2 A B) = (term74 A B).
Proof. exact (MK_COMB (@lem44676 A B) (@lem44674 A B)). Qed.
Lemma lem44683 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem44684 {A B : Type'} (P : type475 A B) (Q : type475 A B) : (term77 A B P Q) = (term78 A B P Q).
Proof. exact (@lem44683 (type1413 A B) P Q). Qed.
Lemma lem44685 {A B : Type'} : (term79 A B) = (term80 A B).
Proof. exact (@lem44684 A B (term81 A B) (term82 A B)). Qed.
Lemma lem44686 {A B : Type'} (r : type1413 A B) : (term83 A B r) = (term68 A B r).
Proof. exact (eq_refl (term83 A B r)). Qed.
Lemma lem44687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44688 {A B : Type'} (r : type1413 A B) : (term84 A B r) = (term69 A B r).
Proof. exact (MK_COMB (@lem44687) (@lem44686 A B r)). Qed.
Lemma lem44689 {A B : Type'} (r : type1413 A B) : (term85 A B r) = (term66 A B r).
Proof. exact (eq_refl (term85 A B r)). Qed.
Lemma lem44690 {A B : Type'} (r : type1413 A B) : (term86 A B r) = (term71 A B r).
Proof. exact (MK_COMB (@lem44688 A B r) (@lem44689 A B r)). Qed.
Lemma lem44691 {A B : Type'} : (term87 A B) = (term72 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44690 A B r)). Qed.
Lemma lem44692 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44693 {A B : Type'} : (term79 A B) = (term73 A B).
Proof. exact (MK_COMB (@lem44692 A B) (@lem44691 A B)). Qed.
Lemma lem44694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44695 {A B : Type'} : (term88 A B) = (term89 A B).
Proof. exact (MK_COMB (@lem44694) (@lem44693 A B)). Qed.
Lemma lem44696 {A B : Type'} (r : type1413 A B) : (term83 A B r) = (term68 A B r).
Proof. exact (eq_refl (term83 A B r)). Qed.
Lemma lem44697 {A B : Type'} : (term90 A B) = (term81 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44696 A B r)). Qed.
Lemma lem44698 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44699 {A B : Type'} : (term91 A B) = (term92 A B).
Proof. exact (MK_COMB (@lem44698 A B) (@lem44697 A B)). Qed.
Lemma lem44700 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44701 {A B : Type'} : (term93 A B) = (term94 A B).
Proof. exact (MK_COMB (@lem44700) (@lem44699 A B)). Qed.
Lemma lem44702 {A B : Type'} (r : type1413 A B) : (term85 A B r) = (term66 A B r).
Proof. exact (eq_refl (term85 A B r)). Qed.
Lemma lem44703 {A B : Type'} : (term95 A B) = (term82 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44702 A B r)). Qed.
Lemma lem44704 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44705 {A B : Type'} : (term96 A B) = (term97 A B).
Proof. exact (MK_COMB (@lem44704 A B) (@lem44703 A B)). Qed.
Lemma lem44706 {A B : Type'} : (term80 A B) = (term98 A B).
Proof. exact (MK_COMB (@lem44701 A B) (@lem44705 A B)). Qed.
Lemma lem44707 {A B : Type'} : ((term79 A B) = (term80 A B)) = ((term73 A B) = (term98 A B)).
Proof. exact (MK_COMB (@lem44695 A B) (@lem44706 A B)). Qed.
Lemma lem44708 {A B : Type'} : (term73 A B) = (term98 A B).
Proof. exact (EQ_MP (@lem44707 A B) (@lem44685 A B)). Qed.
Lemma lem44821 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem44822 {A B : Type'} : (term74 A B) = (term99 A B).
Proof. exact (MK_COMB (@lem44821 A B) (@lem44708 A B)). Qed.
Lemma lem44824 {A : Type'} (P : A -> Prop) (Q : Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem44825 {A : Type'} (P : A -> Prop) (Q : Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (@lem44824 A P Q). Qed.
Lemma lem44826 {A B : Type'} (r : type1413 A B) : (term102 A B r) = (term103 A B r).
Proof. exact (@lem44825 A (term18 A B r) (term62 A B r)). Qed.
Lemma lem44827 {A B : Type'} (r : type1413 A B) (a : A) : (term57 A B r a) = (term17 A B r a).
Proof. exact (eq_refl (term57 A B r a)). Qed.
Lemma lem44828 {A B : Type'} (r : type1413 A B) : (term104 A B r) = (term18 A B r).
Proof. exact (fun_ext (fun a : A => @lem44827 A B r a)). Qed.
Lemma lem44829 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44830 {A B : Type'} (r : type1413 A B) : (term105 A B r) = (term19 A B r).
Proof. exact (MK_COMB (@lem44829 A) (@lem44828 A B r)). Qed.
Lemma lem44831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem44832 {A B : Type'} (r : type1413 A B) : (term106 A B r) = (term67 A B r).
Proof. exact (MK_COMB (@lem44831) (@lem44830 A B r)). Qed.
Lemma lem44833 {A B : Type'} (r : type1413 A B) : (term62 A B r) = (term62 A B r).
Proof. exact (eq_refl (term62 A B r)). Qed.
Lemma lem44834 {A B : Type'} (r : type1413 A B) : (term102 A B r) = (term68 A B r).
Proof. exact (MK_COMB (@lem44832 A B r) (@lem44833 A B r)). Qed.
Lemma lem44835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44836 {A B : Type'} (r : type1413 A B) : (term107 A B r) = (term108 A B r).
Proof. exact (MK_COMB (@lem44835) (@lem44834 A B r)). Qed.
Lemma lem44837 {A B : Type'} (r : type1413 A B) (a : A) : (term57 A B r a) = (term17 A B r a).
Proof. exact (eq_refl (term57 A B r a)). Qed.
Lemma lem44838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem44839 {A B : Type'} (r : type1413 A B) (a : A) : (term109 A B r a) = (term110 A B r a).
Proof. exact (MK_COMB (@lem44838) (@lem44837 A B r a)). Qed.
Lemma lem44840 {A B : Type'} (r : type1413 A B) : (term62 A B r) = (term62 A B r).
Proof. exact (eq_refl (term62 A B r)). Qed.
Lemma lem44841 {A B : Type'} (a : A) (r : type1413 A B) : (term111 A B a r) = (term112 A B a r).
Proof. exact (MK_COMB (@lem44839 A B r a) (@lem44840 A B r)). Qed.
Lemma lem44842 {A B : Type'} (r : type1413 A B) : (term113 A B r) = (term114 A B r).
Proof. exact (fun_ext (fun a : A => @lem44841 A B a r)). Qed.
Lemma lem44843 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44844 {A B : Type'} (r : type1413 A B) : (term103 A B r) = (term115 A B r).
Proof. exact (MK_COMB (@lem44843 A) (@lem44842 A B r)). Qed.
Lemma lem44845 {A B : Type'} (r : type1413 A B) : ((term102 A B r) = (term103 A B r)) = ((term68 A B r) = (term115 A B r)).
Proof. exact (MK_COMB (@lem44836 A B r) (@lem44844 A B r)). Qed.
Lemma lem44846 {A B : Type'} (r : type1413 A B) : (term68 A B r) = (term115 A B r).
Proof. exact (EQ_MP (@lem44845 A B r) (@lem44826 A B r)). Qed.
Lemma lem44848 {A : Type'} (P : A -> Prop) (Q : Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem44849 {B : Type'} (P : B -> Prop) (Q : Prop) : (term100 B P Q) = (term101 B P Q).
Proof. exact (@lem44848 B P Q). Qed.
Lemma lem44850 {A B : Type'} (a : A) (r : type1413 A B) : (term116 A B a r) = (term117 A B a r).
Proof. exact (@lem44849 B (term16 A B r a) (term62 A B r)). Qed.
Lemma lem44851 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term49 A B r a b) = (r = (@mk_pair A B a b)).
Proof. exact (eq_refl (term49 A B r a b)). Qed.
Lemma lem44852 {A B : Type'} (r : type1413 A B) (a : A) : (term118 A B r a) = (term16 A B r a).
Proof. exact (fun_ext (fun b : B => @lem44851 A B r a b)). Qed.
Lemma lem44853 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44854 {A B : Type'} (r : type1413 A B) (a : A) : (term119 A B r a) = (term17 A B r a).
Proof. exact (MK_COMB (@lem44853 B) (@lem44852 A B r a)). Qed.
Lemma lem44855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem44856 {A B : Type'} (r : type1413 A B) (a : A) : (term120 A B r a) = (term110 A B r a).
Proof. exact (MK_COMB (@lem44855) (@lem44854 A B r a)). Qed.
Lemma lem44857 {A B : Type'} (r : type1413 A B) : (term62 A B r) = (term62 A B r).
Proof. exact (eq_refl (term62 A B r)). Qed.
Lemma lem44858 {A B : Type'} (a : A) (r : type1413 A B) : (term116 A B a r) = (term112 A B a r).
Proof. exact (MK_COMB (@lem44856 A B r a) (@lem44857 A B r)). Qed.
Lemma lem44859 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44860 {A B : Type'} (a : A) (r : type1413 A B) : (term121 A B a r) = (term122 A B a r).
Proof. exact (MK_COMB (@lem44859) (@lem44858 A B a r)). Qed.
Lemma lem44861 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term49 A B r a b) = (r = (@mk_pair A B a b)).
Proof. exact (eq_refl (term49 A B r a b)). Qed.
Lemma lem44862 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem44863 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term123 A B r a b) = (term124 A B r a b).
Proof. exact (MK_COMB (@lem44862) (@lem44861 A B r a b)). Qed.
Lemma lem44864 {A B : Type'} (r : type1413 A B) : (term62 A B r) = (term62 A B r).
Proof. exact (eq_refl (term62 A B r)). Qed.
Lemma lem44865 {A B : Type'} (a : A) (b : B) (r : type1413 A B) : (term125 A B a b r) = (term126 A B a b r).
Proof. exact (MK_COMB (@lem44863 A B r a b) (@lem44864 A B r)). Qed.
Lemma lem44866 {A B : Type'} (a : A) (r : type1413 A B) : (term127 A B a r) = (term128 A B a r).
Proof. exact (fun_ext (fun b : B => @lem44865 A B a b r)). Qed.
Lemma lem44867 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44868 {A B : Type'} (a : A) (r : type1413 A B) : (term117 A B a r) = (term129 A B a r).
Proof. exact (MK_COMB (@lem44867 B) (@lem44866 A B a r)). Qed.
Lemma lem44869 {A B : Type'} (a : A) (r : type1413 A B) : ((term116 A B a r) = (term117 A B a r)) = ((term112 A B a r) = (term129 A B a r)).
Proof. exact (MK_COMB (@lem44860 A B a r) (@lem44868 A B a r)). Qed.
Lemma lem44870 {A B : Type'} (a : A) (r : type1413 A B) : (term112 A B a r) = (term129 A B a r).
Proof. exact (EQ_MP (@lem44869 A B a r) (@lem44850 A B a r)). Qed.
Lemma lem44871 {A B : Type'} (r : type1413 A B) : (term114 A B r) = (term130 A B r).
Proof. exact (fun_ext (fun a : A => @lem44870 A B a r)). Qed.
Lemma lem44872 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44873 {A B : Type'} (r : type1413 A B) : (term115 A B r) = (term131 A B r).
Proof. exact (MK_COMB (@lem44872 A) (@lem44871 A B r)). Qed.
Lemma lem44874 {A B : Type'} (r : type1413 A B) : (term68 A B r) = (term131 A B r).
Proof. exact (TRANS (@lem44846 A B r) (@lem44873 A B r)). Qed.
Lemma lem44875 {A B : Type'} : (term81 A B) = (term132 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44874 A B r)). Qed.
Lemma lem44876 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44877 {A B : Type'} : (term92 A B) = (term133 A B).
Proof. exact (MK_COMB (@lem44876 A B) (@lem44875 A B)). Qed.
Lemma lem44879 {A B : Type'} (P : type1413 A B) : (term134 A B P) = (term135 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem44880 {A B : Type'} (P : type468 A B) : (term136 A B P) = (term137 A B P).
Proof. exact (@lem44879 (type1413 A B) A P). Qed.
Lemma lem44881 {A B : Type'} : (term138 A B) = (term139 A B).
Proof. exact (@lem44880 A B (term140 A B)). Qed.
Lemma lem44882 {A B : Type'} (r : type1413 A B) : (term141 A B r) = (term130 A B r).
Proof. exact (eq_refl (term141 A B r)). Qed.
Lemma lem44883 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem44884 {A B : Type'} (r : type1413 A B) (a : A) : (term142 A B r a) = (term143 A B r a).
Proof. exact (MK_COMB (@lem44882 A B r) (@lem44883 A a)). Qed.
Lemma lem44885 {A B : Type'} (a : A) (r : type1413 A B) : (term143 A B r a) = (term129 A B a r).
Proof. exact (eq_refl (term143 A B r a)). Qed.
Lemma lem44886 {A B : Type'} (a : A) (r : type1413 A B) : (term142 A B r a) = (term129 A B a r).
Proof. exact (TRANS (@lem44884 A B r a) (@lem44885 A B a r)). Qed.
Lemma lem44887 {A B : Type'} (r : type1413 A B) : (term144 A B r) = (term130 A B r).
Proof. exact (fun_ext (fun a : A => @lem44886 A B a r)). Qed.
Lemma lem44888 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem44889 {A B : Type'} (r : type1413 A B) : (term145 A B r) = (term131 A B r).
Proof. exact (MK_COMB (@lem44888 A) (@lem44887 A B r)). Qed.
Lemma lem44890 {A B : Type'} : (term146 A B) = (term132 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44889 A B r)). Qed.
Lemma lem44891 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44892 {A B : Type'} : (term138 A B) = (term133 A B).
Proof. exact (MK_COMB (@lem44891 A B) (@lem44890 A B)). Qed.
Lemma lem44893 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44894 {A B : Type'} : (term147 A B) = (term148 A B).
Proof. exact (MK_COMB (@lem44893) (@lem44892 A B)). Qed.
Lemma lem44895 {A B : Type'} (r : type1413 A B) : (term141 A B r) = (term130 A B r).
Proof. exact (eq_refl (term141 A B r)). Qed.
Lemma lem44896 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (a r) = (a r).
Proof. exact (eq_refl (a r)). Qed.
Lemma lem44897 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term149 A B a r) = (term150 A B a r).
Proof. exact (MK_COMB (@lem44895 A B r) (@lem44896 A B a r)). Qed.
Lemma lem44898 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term150 A B a r) = (term151 A B a r).
Proof. exact (eq_refl (term150 A B a r)). Qed.
Lemma lem44899 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term149 A B a r) = (term151 A B a r).
Proof. exact (TRANS (@lem44897 A B a r) (@lem44898 A B a r)). Qed.
Lemma lem44900 {A B : Type'} (a : type473 A B) : (term152 A B a) = (term153 A B a).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44899 A B a r)). Qed.
Lemma lem44901 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44902 {A B : Type'} (a : type473 A B) : (term154 A B a) = (term155 A B a).
Proof. exact (MK_COMB (@lem44901 A B) (@lem44900 A B a)). Qed.
Lemma lem44903 {A B : Type'} : (term156 A B) = (term157 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem44902 A B a)). Qed.
Lemma lem44904 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem44905 {A B : Type'} : (term139 A B) = (term158 A B).
Proof. exact (MK_COMB (@lem44904 A B) (@lem44903 A B)). Qed.
Lemma lem44906 {A B : Type'} : ((term138 A B) = (term139 A B)) = ((term133 A B) = (term158 A B)).
Proof. exact (MK_COMB (@lem44894 A B) (@lem44905 A B)). Qed.
Lemma lem44907 {A B : Type'} : (term133 A B) = (term158 A B).
Proof. exact (EQ_MP (@lem44906 A B) (@lem44881 A B)). Qed.
Lemma lem44909 {A B : Type'} (P : type1413 A B) : (term134 A B P) = (term135 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem44910 {A B : Type'} (P : type469 A B) : (term159 A B P) = (term160 A B P).
Proof. exact (@lem44909 (type1413 A B) B P). Qed.
Lemma lem44911 {A B : Type'} (a : type473 A B) : (term161 A B a) = (term162 A B a).
Proof. exact (@lem44910 A B (term163 A B a)). Qed.
Lemma lem44912 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term164 A B a r) = (term165 A B a r).
Proof. exact (eq_refl (term164 A B a r)). Qed.
Lemma lem44913 {B : Type'} (b : B) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem44914 {A B : Type'} (a : type473 A B) (r : type1413 A B) (b : B) : (term166 A B a r b) = (term167 A B a r b).
Proof. exact (MK_COMB (@lem44912 A B a r) (@lem44913 B b)). Qed.
Lemma lem44915 {A B : Type'} (a : type473 A B) (b : B) (r : type1413 A B) : (term167 A B a r b) = (term168 A B a b r).
Proof. exact (eq_refl (term167 A B a r b)). Qed.
Lemma lem44916 {A B : Type'} (a : type473 A B) (b : B) (r : type1413 A B) : (term166 A B a r b) = (term168 A B a b r).
Proof. exact (TRANS (@lem44914 A B a r b) (@lem44915 A B a b r)). Qed.
Lemma lem44917 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term169 A B a r) = (term165 A B a r).
Proof. exact (fun_ext (fun b : B => @lem44916 A B a b r)). Qed.
Lemma lem44918 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem44919 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term170 A B a r) = (term151 A B a r).
Proof. exact (MK_COMB (@lem44918 B) (@lem44917 A B a r)). Qed.
Lemma lem44920 {A B : Type'} (a : type473 A B) : (term171 A B a) = (term153 A B a).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44919 A B a r)). Qed.
Lemma lem44921 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44922 {A B : Type'} (a : type473 A B) : (term161 A B a) = (term155 A B a).
Proof. exact (MK_COMB (@lem44921 A B) (@lem44920 A B a)). Qed.
Lemma lem44923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44924 {A B : Type'} (a : type473 A B) : (term172 A B a) = (term173 A B a).
Proof. exact (MK_COMB (@lem44923) (@lem44922 A B a)). Qed.
Lemma lem44925 {A B : Type'} (a : type473 A B) (r : type1413 A B) : (term164 A B a r) = (term165 A B a r).
Proof. exact (eq_refl (term164 A B a r)). Qed.
Lemma lem44926 {A B : Type'} (b : type474 A B) (r : type1413 A B) : (b r) = (b r).
Proof. exact (eq_refl (b r)). Qed.
Lemma lem44927 {A B : Type'} (a : type473 A B) (b : type474 A B) (r : type1413 A B) : (term174 A B a b r) = (term175 A B a b r).
Proof. exact (MK_COMB (@lem44925 A B a r) (@lem44926 A B b r)). Qed.
Lemma lem44928 {A B : Type'} (a : type473 A B) (b : type474 A B) (r : type1413 A B) : (term175 A B a b r) = (term176 A B a b r).
Proof. exact (eq_refl (term175 A B a b r)). Qed.
Lemma lem44929 {A B : Type'} (a : type473 A B) (b : type474 A B) (r : type1413 A B) : (term174 A B a b r) = (term176 A B a b r).
Proof. exact (TRANS (@lem44927 A B a b r) (@lem44928 A B a b r)). Qed.
Lemma lem44930 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term177 A B a b) = (term178 A B a b).
Proof. exact (fun_ext (fun r : type1413 A B => @lem44929 A B a b r)). Qed.
Lemma lem44931 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem44932 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term179 A B a b) = (term180 A B a b).
Proof. exact (MK_COMB (@lem44931 A B) (@lem44930 A B a b)). Qed.
Lemma lem44933 {A B : Type'} (a : type473 A B) : (term181 A B a) = (term182 A B a).
Proof. exact (fun_ext (fun b : type474 A B => @lem44932 A B a b)). Qed.
Lemma lem44934 {A B : Type'} : (@ex ((A -> B -> Prop) -> B)) = (@ex ((A -> B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> B))). Qed.
Lemma lem44935 {A B : Type'} (a : type473 A B) : (term162 A B a) = (term183 A B a).
Proof. exact (MK_COMB (@lem44934 A B) (@lem44933 A B a)). Qed.
Lemma lem44936 {A B : Type'} (a : type473 A B) : ((term161 A B a) = (term162 A B a)) = ((term155 A B a) = (term183 A B a)).
Proof. exact (MK_COMB (@lem44924 A B a) (@lem44935 A B a)). Qed.
Lemma lem44937 {A B : Type'} (a : type473 A B) : (term155 A B a) = (term183 A B a).
Proof. exact (EQ_MP (@lem44936 A B a) (@lem44911 A B a)). Qed.
Lemma lem44938 {A B : Type'} : (term157 A B) = (term184 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem44937 A B a)). Qed.
Lemma lem44939 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem44940 {A B : Type'} : (term158 A B) = (term185 A B).
Proof. exact (MK_COMB (@lem44939 A B) (@lem44938 A B)). Qed.
Lemma lem44941 {A B : Type'} : (term133 A B) = (term185 A B).
Proof. exact (TRANS (@lem44907 A B) (@lem44940 A B)). Qed.
Lemma lem44942 {A B : Type'} : (term92 A B) = (term185 A B).
Proof. exact (TRANS (@lem44877 A B) (@lem44941 A B)). Qed.
Lemma lem44943 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44944 {A B : Type'} : (term94 A B) = (term186 A B).
Proof. exact (MK_COMB (@lem44943) (@lem44942 A B)). Qed.
Lemma lem44945 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (eq_refl (term97 A B)). Qed.
Lemma lem44946 {A B : Type'} : (term98 A B) = (term187 A B).
Proof. exact (MK_COMB (@lem44944 A B) (@lem44945 A B)). Qed.
Lemma lem44948 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem44949 {A B : Type'} (P : type89 A B) (Q : Prop) : (term190 A B P Q) = (term191 A B P Q).
Proof. exact (@lem44948 (type473 A B) P Q). Qed.
Lemma lem44950 {A B : Type'} : (term192 A B) = (term193 A B).
Proof. exact (@lem44949 A B (term184 A B) (term97 A B)). Qed.
Lemma lem44951 {A B : Type'} (a : type473 A B) : (term194 A B a) = (term183 A B a).
Proof. exact (eq_refl (term194 A B a)). Qed.
Lemma lem44952 {A B : Type'} : (term195 A B) = (term184 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem44951 A B a)). Qed.
Lemma lem44953 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem44954 {A B : Type'} : (term196 A B) = (term185 A B).
Proof. exact (MK_COMB (@lem44953 A B) (@lem44952 A B)). Qed.
Lemma lem44955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44956 {A B : Type'} : (term197 A B) = (term186 A B).
Proof. exact (MK_COMB (@lem44955) (@lem44954 A B)). Qed.
Lemma lem44957 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (eq_refl (term97 A B)). Qed.
Lemma lem44958 {A B : Type'} : (term192 A B) = (term187 A B).
Proof. exact (MK_COMB (@lem44956 A B) (@lem44957 A B)). Qed.
Lemma lem44959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44960 {A B : Type'} : (term198 A B) = (term199 A B).
Proof. exact (MK_COMB (@lem44959) (@lem44958 A B)). Qed.
Lemma lem44961 {A B : Type'} (a : type473 A B) : (term194 A B a) = (term183 A B a).
Proof. exact (eq_refl (term194 A B a)). Qed.
Lemma lem44962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44963 {A B : Type'} (a : type473 A B) : (term200 A B a) = (term201 A B a).
Proof. exact (MK_COMB (@lem44962) (@lem44961 A B a)). Qed.
Lemma lem44964 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (eq_refl (term97 A B)). Qed.
Lemma lem44965 {A B : Type'} (a : type473 A B) : (term202 A B a) = (term203 A B a).
Proof. exact (MK_COMB (@lem44963 A B a) (@lem44964 A B)). Qed.
Lemma lem44966 {A B : Type'} : (term204 A B) = (term205 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem44965 A B a)). Qed.
Lemma lem44967 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem44968 {A B : Type'} : (term193 A B) = (term206 A B).
Proof. exact (MK_COMB (@lem44967 A B) (@lem44966 A B)). Qed.
Lemma lem44969 {A B : Type'} : ((term192 A B) = (term193 A B)) = ((term187 A B) = (term206 A B)).
Proof. exact (MK_COMB (@lem44960 A B) (@lem44968 A B)). Qed.
Lemma lem44970 {A B : Type'} : (term187 A B) = (term206 A B).
Proof. exact (EQ_MP (@lem44969 A B) (@lem44950 A B)). Qed.
Lemma lem44972 {A : Type'} (P : A -> Prop) (Q : Prop) : (term188 A P Q) = (term189 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem44973 {A B : Type'} (P : type90 A B) (Q : Prop) : (term207 A B P Q) = (term208 A B P Q).
Proof. exact (@lem44972 (type474 A B) P Q). Qed.
Lemma lem44974 {A B : Type'} (a : type473 A B) : (term209 A B a) = (term210 A B a).
Proof. exact (@lem44973 A B (term182 A B a) (term97 A B)). Qed.
Lemma lem44975 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term211 A B a b) = (term180 A B a b).
Proof. exact (eq_refl (term211 A B a b)). Qed.
Lemma lem44976 {A B : Type'} (a : type473 A B) : (term212 A B a) = (term182 A B a).
Proof. exact (fun_ext (fun b : type474 A B => @lem44975 A B a b)). Qed.
Lemma lem44977 {A B : Type'} : (@ex ((A -> B -> Prop) -> B)) = (@ex ((A -> B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> B))). Qed.
Lemma lem44978 {A B : Type'} (a : type473 A B) : (term213 A B a) = (term183 A B a).
Proof. exact (MK_COMB (@lem44977 A B) (@lem44976 A B a)). Qed.
Lemma lem44979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44980 {A B : Type'} (a : type473 A B) : (term214 A B a) = (term201 A B a).
Proof. exact (MK_COMB (@lem44979) (@lem44978 A B a)). Qed.
Lemma lem44981 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (eq_refl (term97 A B)). Qed.
Lemma lem44982 {A B : Type'} (a : type473 A B) : (term209 A B a) = (term203 A B a).
Proof. exact (MK_COMB (@lem44980 A B a) (@lem44981 A B)). Qed.
Lemma lem44983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem44984 {A B : Type'} (a : type473 A B) : (term215 A B a) = (term216 A B a).
Proof. exact (MK_COMB (@lem44983) (@lem44982 A B a)). Qed.
Lemma lem44985 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term211 A B a b) = (term180 A B a b).
Proof. exact (eq_refl (term211 A B a b)). Qed.
Lemma lem44986 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem44987 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term217 A B a b) = (term218 A B a b).
Proof. exact (MK_COMB (@lem44986) (@lem44985 A B a b)). Qed.
Lemma lem44988 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (eq_refl (term97 A B)). Qed.
Lemma lem44989 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term219 A B a b) = (term220 A B a b).
Proof. exact (MK_COMB (@lem44987 A B a b) (@lem44988 A B)). Qed.
Lemma lem44990 {A B : Type'} (a : type473 A B) : (term221 A B a) = (term222 A B a).
Proof. exact (fun_ext (fun b : type474 A B => @lem44989 A B a b)). Qed.
Lemma lem44991 {A B : Type'} : (@ex ((A -> B -> Prop) -> B)) = (@ex ((A -> B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> B))). Qed.
Lemma lem44992 {A B : Type'} (a : type473 A B) : (term210 A B a) = (term223 A B a).
Proof. exact (MK_COMB (@lem44991 A B) (@lem44990 A B a)). Qed.
Lemma lem44993 {A B : Type'} (a : type473 A B) : ((term209 A B a) = (term210 A B a)) = ((term203 A B a) = (term223 A B a)).
Proof. exact (MK_COMB (@lem44984 A B a) (@lem44992 A B a)). Qed.
Lemma lem44994 {A B : Type'} (a : type473 A B) : (term203 A B a) = (term223 A B a).
Proof. exact (EQ_MP (@lem44993 A B a) (@lem44974 A B a)). Qed.
Lemma lem44995 {A B : Type'} : (term205 A B) = (term224 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem44994 A B a)). Qed.
Lemma lem44996 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem44997 {A B : Type'} : (term206 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem44996 A B) (@lem44995 A B)). Qed.
Lemma lem44998 {A B : Type'} : (term187 A B) = (term225 A B).
Proof. exact (TRANS (@lem44970 A B) (@lem44997 A B)). Qed.
Lemma lem44999 {A B : Type'} : (term98 A B) = (term225 A B).
Proof. exact (TRANS (@lem44946 A B) (@lem44998 A B)). Qed.
Lemma lem45000 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem45001 {A B : Type'} : (term99 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem45000 A B) (@lem44999 A B)). Qed.
Lemma lem45003 {A : Type'} (P : Prop) (Q : A -> Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem45004 {A B : Type'} (P : Prop) (Q : type89 A B) : (term229 A B P Q) = (term230 A B P Q).
Proof. exact (@lem45003 (type473 A B) P Q). Qed.
Lemma lem45005 {A B : Type'} : (term231 A B) = (term232 A B).
Proof. exact (@lem45004 A B (term1 A B) (term224 A B)). Qed.
Lemma lem45006 {A B : Type'} (a : type473 A B) : (term233 A B a) = (term223 A B a).
Proof. exact (eq_refl (term233 A B a)). Qed.
Lemma lem45007 {A B : Type'} : (term234 A B) = (term224 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem45006 A B a)). Qed.
Lemma lem45008 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem45009 {A B : Type'} : (term235 A B) = (term225 A B).
Proof. exact (MK_COMB (@lem45008 A B) (@lem45007 A B)). Qed.
Lemma lem45010 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem45011 {A B : Type'} : (term231 A B) = (term226 A B).
Proof. exact (MK_COMB (@lem45010 A B) (@lem45009 A B)). Qed.
Lemma lem45012 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45013 {A B : Type'} : (term236 A B) = (term237 A B).
Proof. exact (MK_COMB (@lem45012) (@lem45011 A B)). Qed.
Lemma lem45014 {A B : Type'} (a : type473 A B) : (term233 A B a) = (term223 A B a).
Proof. exact (eq_refl (term233 A B a)). Qed.
Lemma lem45015 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem45016 {A B : Type'} (a : type473 A B) : (term238 A B a) = (term239 A B a).
Proof. exact (MK_COMB (@lem45015 A B) (@lem45014 A B a)). Qed.
Lemma lem45017 {A B : Type'} : (term240 A B) = (term241 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem45016 A B a)). Qed.
Lemma lem45018 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem45019 {A B : Type'} : (term232 A B) = (term242 A B).
Proof. exact (MK_COMB (@lem45018 A B) (@lem45017 A B)). Qed.
Lemma lem45020 {A B : Type'} : ((term231 A B) = (term232 A B)) = ((term226 A B) = (term242 A B)).
Proof. exact (MK_COMB (@lem45013 A B) (@lem45019 A B)). Qed.
Lemma lem45021 {A B : Type'} : (term226 A B) = (term242 A B).
Proof. exact (EQ_MP (@lem45020 A B) (@lem45005 A B)). Qed.
Lemma lem45023 {A : Type'} (P : Prop) (Q : A -> Prop) : (term227 A P Q) = (term228 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem45024 {A B : Type'} (P : Prop) (Q : type90 A B) : (term243 A B P Q) = (term244 A B P Q).
Proof. exact (@lem45023 (type474 A B) P Q). Qed.
Lemma lem45025 {A B : Type'} (a : type473 A B) : (term245 A B a) = (term246 A B a).
Proof. exact (@lem45024 A B (term1 A B) (term222 A B a)). Qed.
Lemma lem45026 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term247 A B a b) = (term220 A B a b).
Proof. exact (eq_refl (term247 A B a b)). Qed.
Lemma lem45027 {A B : Type'} (a : type473 A B) : (term248 A B a) = (term222 A B a).
Proof. exact (fun_ext (fun b : type474 A B => @lem45026 A B a b)). Qed.
Lemma lem45028 {A B : Type'} : (@ex ((A -> B -> Prop) -> B)) = (@ex ((A -> B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> B))). Qed.
Lemma lem45029 {A B : Type'} (a : type473 A B) : (term249 A B a) = (term223 A B a).
Proof. exact (MK_COMB (@lem45028 A B) (@lem45027 A B a)). Qed.
Lemma lem45030 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem45031 {A B : Type'} (a : type473 A B) : (term245 A B a) = (term239 A B a).
Proof. exact (MK_COMB (@lem45030 A B) (@lem45029 A B a)). Qed.
Lemma lem45032 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45033 {A B : Type'} (a : type473 A B) : (term250 A B a) = (term251 A B a).
Proof. exact (MK_COMB (@lem45032) (@lem45031 A B a)). Qed.
Lemma lem45034 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term247 A B a b) = (term220 A B a b).
Proof. exact (eq_refl (term247 A B a b)). Qed.
Lemma lem45035 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (eq_refl (term24 A B)). Qed.
Lemma lem45036 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term252 A B a b) = (term253 A B a b).
Proof. exact (MK_COMB (@lem45035 A B) (@lem45034 A B a b)). Qed.
Lemma lem45037 {A B : Type'} (a : type473 A B) : (term254 A B a) = (term255 A B a).
Proof. exact (fun_ext (fun b : type474 A B => @lem45036 A B a b)). Qed.
Lemma lem45038 {A B : Type'} : (@ex ((A -> B -> Prop) -> B)) = (@ex ((A -> B -> Prop) -> B)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> B))). Qed.
Lemma lem45039 {A B : Type'} (a : type473 A B) : (term246 A B a) = (term256 A B a).
Proof. exact (MK_COMB (@lem45038 A B) (@lem45037 A B a)). Qed.
Lemma lem45040 {A B : Type'} (a : type473 A B) : ((term245 A B a) = (term246 A B a)) = ((term239 A B a) = (term256 A B a)).
Proof. exact (MK_COMB (@lem45033 A B a) (@lem45039 A B a)). Qed.
Lemma lem45041 {A B : Type'} (a : type473 A B) : (term239 A B a) = (term256 A B a).
Proof. exact (EQ_MP (@lem45040 A B a) (@lem45025 A B a)). Qed.
Lemma lem45042 {A B : Type'} : (term241 A B) = (term257 A B).
Proof. exact (fun_ext (fun a : type473 A B => @lem45041 A B a)). Qed.
Lemma lem45043 {A B : Type'} : (@ex ((A -> B -> Prop) -> A)) = (@ex ((A -> B -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> B -> Prop) -> A))). Qed.
Lemma lem45044 {A B : Type'} : (term242 A B) = (term258 A B).
Proof. exact (MK_COMB (@lem45043 A B) (@lem45042 A B)). Qed.
Lemma lem45045 {A B : Type'} : (term226 A B) = (term258 A B).
Proof. exact (TRANS (@lem45021 A B) (@lem45044 A B)). Qed.
Lemma lem45046 {A B : Type'} : (term99 A B) = (term258 A B).
Proof. exact (TRANS (@lem45001 A B) (@lem45045 A B)). Qed.
Lemma lem45047 {A B : Type'} : (term74 A B) = (term258 A B).
Proof. exact (TRANS (@lem44822 A B) (@lem45046 A B)). Qed.
Lemma lem45048 {A B : Type'} : (term2 A B) = (term258 A B).
Proof. exact (TRANS (@lem44677 A B) (@lem45047 A B)). Qed.
Lemma lem45049 {A B : Type'} (h1 : term2 A B) : term258 A B.
Proof. exact (EQ_MP (@lem45048 A B) (@lem44592 A B h1)). Qed.
Lemma lem45050 {A B : Type'} (a : type473 A B) (h1 : term256 A B a) : term256 A B a.
Proof. exact (h1). Qed.
Lemma lem45051 {A B : Type'} (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term253 A B a b.
Proof. exact (h1). Qed.
Lemma lem45052 {A B : Type'} (x : A) (h1 : term38 A B x) : term38 A B x.
Proof. exact (h1). Qed.
Lemma lem45062 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem45073 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term51 A B r a b) = (term51 A B r a b).
Proof. exact (eq_refl (term51 A B r a b)). Qed.
Lemma lem45074 {A B : Type'} (r : type1413 A B) (a : A) : (term53 A B r a) = (term53 A B r a).
Proof. exact (fun_ext (fun b : B => @lem45073 A B r a b)). Qed.
Lemma lem45075 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45076 {A B : Type'} (r : type1413 A B) (a : A) : (term54 A B r a) = (term54 A B r a).
Proof. exact (MK_COMB (@lem45075 B) (@lem45074 A B r a)). Qed.
Lemma lem45077 {A B : Type'} (r : type1413 A B) : (term60 A B r) = (term60 A B r).
Proof. exact (fun_ext (fun a : A => @lem45076 A B r a)). Qed.
Lemma lem45078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45079 {A B : Type'} (r : type1413 A B) : (term61 A B r) = (term61 A B r).
Proof. exact (MK_COMB (@lem45078 A) (@lem45077 A B r)). Qed.
Lemma lem45080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem45081 {A B : Type'} (r : type1413 A B) : (term64 A B r) = (term64 A B r).
Proof. exact (MK_COMB (@lem45080) (@lem45079 A B r)). Qed.
Lemma lem45082 {A B : Type'} (r : type1413 A B) : (term66 A B r) = (term66 A B r).
Proof. exact (MK_COMB (@lem45081 A B r) (@lem45062 A B r)). Qed.
Lemma lem45083 {A B : Type'} : (term82 A B) = (term82 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem45082 A B r)). Qed.
Lemma lem45084 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem45085 {A B : Type'} : (term97 A B) = (term97 A B).
Proof. exact (MK_COMB (@lem45084 A B) (@lem45083 A B)). Qed.
Lemma lem45112 {A B : Type'} (a : type473 A B) (b : type474 A B) (r : type1413 A B) : (term176 A B a b r) = (term176 A B a b r).
Proof. exact (eq_refl (term176 A B a b r)). Qed.
Lemma lem45113 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term178 A B a b) = (term178 A B a b).
Proof. exact (fun_ext (fun r : type1413 A B => @lem45112 A B a b r)). Qed.
Lemma lem45114 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem45115 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term180 A B a b) = (term180 A B a b).
Proof. exact (MK_COMB (@lem45114 A B) (@lem45113 A B a b)). Qed.
Lemma lem45116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem45117 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term218 A B a b) = (term218 A B a b).
Proof. exact (MK_COMB (@lem45116) (@lem45115 A B a b)). Qed.
Lemma lem45118 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term220 A B a b) = (term220 A B a b).
Proof. exact (MK_COMB (@lem45117 A B a b) (@lem45085 A B)). Qed.
Lemma lem45127 {A B : Type'} (a : prod A B) : ((term22 A B a) = a) = ((term22 A B a) = a).
Proof. exact (eq_refl ((term22 A B a) = a)). Qed.
Lemma lem45128 {A B : Type'} : (term23 A B) = (term23 A B).
Proof. exact (fun_ext (fun a : prod A B => @lem45127 A B a)). Qed.
Lemma lem45129 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem45130 {A B : Type'} : (term1 A B) = (term1 A B).
Proof. exact (MK_COMB (@lem45129 A B) (@lem45128 A B)). Qed.
Lemma lem45131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem45132 {A B : Type'} : (term24 A B) = (term24 A B).
Proof. exact (MK_COMB (@lem45131) (@lem45130 A B)). Qed.
Lemma lem45133 {A B : Type'} (a : type473 A B) (b : type474 A B) : (term253 A B a b) = (term253 A B a b).
Proof. exact (MK_COMB (@lem45132 A B) (@lem45118 A B a b)). Qed.
Lemma lem45134 {A B : Type'} (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term253 A B a b.
Proof. exact (EQ_MP (@lem45133 A B a b) (@lem45051 A B a b h1)). Qed.
Lemma lem45154 {A B : Type'} (x : A) (y : B) (h1 : term35 A B x y) : term35 A B x y.
Proof. exact (h1). Qed.
Lemma lem45155 {A B : Type'} (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term220 A B a b.
Proof. exact (proj2 (@lem45134 A B a b h1)). Qed.
Lemma lem45157 {A B : Type'} (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term97 A B.
Proof. exact (proj2 (@lem45155 A B a b h1)). Qed.
Lemma lem45162 {A B : Type'} (x : A) (y : B) (h1 : term35 A B x y) : term35 A B x y.
Proof. exact (h1). Qed.
Lemma lem45184 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem45185 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (@lem45184 A P Q). Qed.
Lemma lem45186 {A B : Type'} (r : type1413 A B) : (term261 A B r) = (term262 A B r).
Proof. exact (@lem45185 A (term60 A B r) ((term15 A B r) = r)). Qed.
Lemma lem45187 {A B : Type'} (r : type1413 A B) (a : A) : (term263 A B r a) = (term54 A B r a).
Proof. exact (eq_refl (term263 A B r a)). Qed.
Lemma lem45188 {A B : Type'} (r : type1413 A B) : (term264 A B r) = (term60 A B r).
Proof. exact (fun_ext (fun a : A => @lem45187 A B r a)). Qed.
Lemma lem45189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45190 {A B : Type'} (r : type1413 A B) : (term265 A B r) = (term61 A B r).
Proof. exact (MK_COMB (@lem45189 A) (@lem45188 A B r)). Qed.
Lemma lem45191 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem45192 {A B : Type'} (r : type1413 A B) : (term266 A B r) = (term64 A B r).
Proof. exact (MK_COMB (@lem45191) (@lem45190 A B r)). Qed.
Lemma lem45193 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem45194 {A B : Type'} (r : type1413 A B) : (term261 A B r) = (term66 A B r).
Proof. exact (MK_COMB (@lem45192 A B r) (@lem45193 A B r)). Qed.
Lemma lem45195 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45196 {A B : Type'} (r : type1413 A B) : (term267 A B r) = (term268 A B r).
Proof. exact (MK_COMB (@lem45195) (@lem45194 A B r)). Qed.
Lemma lem45197 {A B : Type'} (r : type1413 A B) (a : A) : (term263 A B r a) = (term54 A B r a).
Proof. exact (eq_refl (term263 A B r a)). Qed.
Lemma lem45198 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem45199 {A B : Type'} (r : type1413 A B) (a : A) : (term269 A B r a) = (term270 A B r a).
Proof. exact (MK_COMB (@lem45198) (@lem45197 A B r a)). Qed.
Lemma lem45200 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem45201 {A B : Type'} (a : A) (r : type1413 A B) : (term271 A B a r) = (term272 A B a r).
Proof. exact (MK_COMB (@lem45199 A B r a) (@lem45200 A B r)). Qed.
Lemma lem45202 {A B : Type'} (r : type1413 A B) : (term273 A B r) = (term274 A B r).
Proof. exact (fun_ext (fun a : A => @lem45201 A B a r)). Qed.
Lemma lem45203 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45204 {A B : Type'} (r : type1413 A B) : (term262 A B r) = (term275 A B r).
Proof. exact (MK_COMB (@lem45203 A) (@lem45202 A B r)). Qed.
Lemma lem45205 {A B : Type'} (r : type1413 A B) : ((term261 A B r) = (term262 A B r)) = ((term66 A B r) = (term275 A B r)).
Proof. exact (MK_COMB (@lem45196 A B r) (@lem45204 A B r)). Qed.
Lemma lem45206 {A B : Type'} (r : type1413 A B) : (term66 A B r) = (term275 A B r).
Proof. exact (EQ_MP (@lem45205 A B r) (@lem45186 A B r)). Qed.
Lemma lem45208 {A : Type'} (P : A -> Prop) (Q : Prop) : (term259 A P Q) = (term260 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem45209 {B : Type'} (P : B -> Prop) (Q : Prop) : (term259 B P Q) = (term260 B P Q).
Proof. exact (@lem45208 B P Q). Qed.
Lemma lem45210 {A B : Type'} (a : A) (r : type1413 A B) : (term276 A B a r) = (term277 A B a r).
Proof. exact (@lem45209 B (term53 A B r a) ((term15 A B r) = r)). Qed.
Lemma lem45211 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term278 A B r a b) = (term51 A B r a b).
Proof. exact (eq_refl (term278 A B r a b)). Qed.
Lemma lem45212 {A B : Type'} (r : type1413 A B) (a : A) : (term279 A B r a) = (term53 A B r a).
Proof. exact (fun_ext (fun b : B => @lem45211 A B r a b)). Qed.
Lemma lem45213 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45214 {A B : Type'} (r : type1413 A B) (a : A) : (term280 A B r a) = (term54 A B r a).
Proof. exact (MK_COMB (@lem45213 B) (@lem45212 A B r a)). Qed.
Lemma lem45215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem45216 {A B : Type'} (r : type1413 A B) (a : A) : (term281 A B r a) = (term270 A B r a).
Proof. exact (MK_COMB (@lem45215) (@lem45214 A B r a)). Qed.
Lemma lem45217 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem45218 {A B : Type'} (a : A) (r : type1413 A B) : (term276 A B a r) = (term272 A B a r).
Proof. exact (MK_COMB (@lem45216 A B r a) (@lem45217 A B r)). Qed.
Lemma lem45219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45220 {A B : Type'} (a : A) (r : type1413 A B) : (term282 A B a r) = (term283 A B a r).
Proof. exact (MK_COMB (@lem45219) (@lem45218 A B a r)). Qed.
Lemma lem45221 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term278 A B r a b) = (term51 A B r a b).
Proof. exact (eq_refl (term278 A B r a b)). Qed.
Lemma lem45222 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem45223 {A B : Type'} (r : type1413 A B) (a : A) (b : B) : (term284 A B r a b) = (term285 A B r a b).
Proof. exact (MK_COMB (@lem45222) (@lem45221 A B r a b)). Qed.
Lemma lem45224 {A B : Type'} (r : type1413 A B) : ((term15 A B r) = r) = ((term15 A B r) = r).
Proof. exact (eq_refl ((term15 A B r) = r)). Qed.
Lemma lem45225 {A B : Type'} (a : A) (b : B) (r : type1413 A B) : (term286 A B a b r) = (term287 A B a b r).
Proof. exact (MK_COMB (@lem45223 A B r a b) (@lem45224 A B r)). Qed.
Lemma lem45226 {A B : Type'} (a : A) (r : type1413 A B) : (term288 A B a r) = (term289 A B a r).
Proof. exact (fun_ext (fun b : B => @lem45225 A B a b r)). Qed.
Lemma lem45227 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45228 {A B : Type'} (a : A) (r : type1413 A B) : (term277 A B a r) = (term290 A B a r).
Proof. exact (MK_COMB (@lem45227 B) (@lem45226 A B a r)). Qed.
Lemma lem45229 {A B : Type'} (a : A) (r : type1413 A B) : ((term276 A B a r) = (term277 A B a r)) = ((term272 A B a r) = (term290 A B a r)).
Proof. exact (MK_COMB (@lem45220 A B a r) (@lem45228 A B a r)). Qed.
Lemma lem45230 {A B : Type'} (a : A) (r : type1413 A B) : (term272 A B a r) = (term290 A B a r).
Proof. exact (EQ_MP (@lem45229 A B a r) (@lem45210 A B a r)). Qed.
Lemma lem45231 {A B : Type'} (r : type1413 A B) : (term274 A B r) = (term291 A B r).
Proof. exact (fun_ext (fun a : A => @lem45230 A B a r)). Qed.
Lemma lem45232 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45233 {A B : Type'} (r : type1413 A B) : (term275 A B r) = (term292 A B r).
Proof. exact (MK_COMB (@lem45232 A) (@lem45231 A B r)). Qed.
Lemma lem45234 {A B : Type'} (r : type1413 A B) : (term66 A B r) = (term292 A B r).
Proof. exact (TRANS (@lem45206 A B r) (@lem45233 A B r)). Qed.
Lemma lem45235 {A B : Type'} : (term82 A B) = (term293 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem45234 A B r)). Qed.
Lemma lem45236 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem45237 {A B : Type'} : (term97 A B) = (term294 A B).
Proof. exact (MK_COMB (@lem45236 A B) (@lem45235 A B)). Qed.
Lemma lem45244 {A B : Type'} (a : A) (b : B) (r : type1413 A B) : (term287 A B a b r) = (term287 A B a b r).
Proof. exact (eq_refl (term287 A B a b r)). Qed.
Lemma lem45245 {A B : Type'} (a : A) (r : type1413 A B) : (term289 A B a r) = (term289 A B a r).
Proof. exact (fun_ext (fun b : B => @lem45244 A B a b r)). Qed.
Lemma lem45246 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem45247 {A B : Type'} (a : A) (r : type1413 A B) : (term290 A B a r) = (term290 A B a r).
Proof. exact (MK_COMB (@lem45246 B) (@lem45245 A B a r)). Qed.
Lemma lem45248 {A B : Type'} (r : type1413 A B) : (term291 A B r) = (term291 A B r).
Proof. exact (fun_ext (fun a : A => @lem45247 A B a r)). Qed.
Lemma lem45249 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem45250 {A B : Type'} (r : type1413 A B) : (term292 A B r) = (term292 A B r).
Proof. exact (MK_COMB (@lem45249 A) (@lem45248 A B r)). Qed.
Lemma lem45251 {A B : Type'} : (term293 A B) = (term293 A B).
Proof. exact (fun_ext (fun r : type1413 A B => @lem45250 A B r)). Qed.
Lemma lem45252 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem45253 {A B : Type'} : (term294 A B) = (term294 A B).
Proof. exact (MK_COMB (@lem45252 A B) (@lem45251 A B)). Qed.
Lemma lem45254 {A B : Type'} : (term97 A B) = (term294 A B).
Proof. exact (TRANS (@lem45237 A B) (@lem45253 A B)). Qed.
Lemma lem45255 {A B : Type'} (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term294 A B.
Proof. exact (EQ_MP (@lem45254 A B) (@lem45157 A B a b h1)). Qed.
Lemma lem45262 {A B : Type'} (_1242 : type1413 A B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term295 A B _1242.
Proof. exact (@lem45255 A B a b h1 _1242). Qed.
Lemma lem45263 {A B : Type'} (_1242 : type1413 A B) : (term295 A B _1242) = (term292 A B _1242).
Proof. exact (eq_refl (term295 A B _1242)). Qed.
Lemma lem45264 {A B : Type'} (_1242 : type1413 A B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term292 A B _1242.
Proof. exact (EQ_MP (@lem45263 A B _1242) (@lem45262 A B _1242 a b h1)). Qed.
Lemma lem45265 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term296 A B _1242 _1243.
Proof. exact (@lem45264 A B _1242 a b h1 _1243). Qed.
Lemma lem45266 {A B : Type'} (_1243 : A) (_1242 : type1413 A B) : (term296 A B _1242 _1243) = (term290 A B _1243 _1242).
Proof. exact (eq_refl (term296 A B _1242 _1243)). Qed.
Lemma lem45267 {A B : Type'} (_1243 : A) (_1242 : type1413 A B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term290 A B _1243 _1242.
Proof. exact (EQ_MP (@lem45266 A B _1243 _1242) (@lem45265 A B _1242 _1243 a b h1)). Qed.
Lemma lem45268 {A B : Type'} (_1243 : A) (_1242 : type1413 A B) (_1244 : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term297 A B _1243 _1242 _1244.
Proof. exact (@lem45267 A B _1243 _1242 a b h1 _1244). Qed.
Lemma lem45269 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) : (term297 A B _1243 _1242 _1244) = (term287 A B _1243 _1244 _1242).
Proof. exact (eq_refl (term297 A B _1243 _1242 _1244)). Qed.
Lemma lem45272 {A B : Type'} (x : A) (y : B) (h1 : term35 A B x y) : term35 A B x y.
Proof. exact (h1). Qed.
Lemma lem45286 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term287 A B _1243 _1244 _1242.
Proof. exact (EQ_MP (@lem45269 A B _1243 _1244 _1242) (@lem45268 A B _1243 _1242 _1244 a b h1)). Qed.
Lemma lem45343 {A B : Type'} (x : type1413 A B) : x = x.
Proof. exact (@lem21386 (type1413 A B) x). Qed.
Lemma lem45344 {A B : Type'} (x : type1413 A B) : x = x.
Proof. exact (@lem45343 A B x). Qed.
Lemma lem45345 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (@mk_pair A B x y).
Proof. exact (@lem45344 A B (@mk_pair A B x y)). Qed.
Lemma lem45346 {A B : Type'} (x : A) (y : B) : term298 A B x y.
Proof. exact (fun h0 : term299 A B x y => @lem45345 A B x y). Qed.
Lemma lem45348 (p : Prop) : (term300 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem45349 {A B : Type'} (x : A) (y : B) : (term298 A B x y) = ((@mk_pair A B x y) = (@mk_pair A B x y)).
Proof. exact (@lem45348 ((@mk_pair A B x y) = (@mk_pair A B x y))). Qed.
Lemma lem45350 {A B : Type'} (x : A) (y : B) : (@mk_pair A B x y) = (@mk_pair A B x y).
Proof. exact (EQ_MP (@lem45349 A B x y) (@lem45346 A B x y)). Qed.
Lemma lem45356 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem45357 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : (term287 A B _1243 _1244 _1242) = (term301 A B _1242 _1243 _1244).
Proof. exact (@lem45356 ((term15 A B _1242) = _1242) (term51 A B _1242 _1243 _1244)). Qed.
Lemma lem45367 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem45368 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : (term302 A B _1243 _1244 _1242) = (term303 A B _1242 _1243 _1244).
Proof. exact (MK_COMB (@lem45367) (@lem45357 A B _1242 _1243 _1244)). Qed.
Lemma lem45378 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : (term301 A B _1242 _1243 _1244) = (term301 A B _1242 _1243 _1244).
Proof. exact (eq_refl (term301 A B _1242 _1243 _1244)). Qed.
Lemma lem45379 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : ((term287 A B _1243 _1244 _1242) = (term301 A B _1242 _1243 _1244)) = ((term301 A B _1242 _1243 _1244) = (term301 A B _1242 _1243 _1244)).
Proof. exact (MK_COMB (@lem45368 A B _1242 _1243 _1244) (@lem45378 A B _1242 _1243 _1244)). Qed.
Lemma lem45381 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem45382 (x : Prop) : (x = x) = True.
Proof. exact (@lem45381 Prop x). Qed.
Lemma lem45383 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : ((term301 A B _1242 _1243 _1244) = (term301 A B _1242 _1243 _1244)) = True.
Proof. exact (@lem45382 (term301 A B _1242 _1243 _1244)). Qed.
Lemma lem45384 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : ((term287 A B _1243 _1244 _1242) = (term301 A B _1242 _1243 _1244)) = True.
Proof. exact (TRANS (@lem45379 A B _1242 _1243 _1244) (@lem45383 A B _1242 _1243 _1244)). Qed.
Lemma lem45385 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : True = ((term287 A B _1243 _1244 _1242) = (term301 A B _1242 _1243 _1244)).
Proof. exact (SYM (@lem45384 A B _1242 _1243 _1244)). Qed.
Lemma lem45386 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : (term287 A B _1243 _1244 _1242) = (term301 A B _1242 _1243 _1244).
Proof. exact (EQ_MP (@lem45385 A B _1242 _1243 _1244) (@lem0)). Qed.
Lemma lem45387 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term301 A B _1242 _1243 _1244.
Proof. exact (EQ_MP (@lem45386 A B _1242 _1243 _1244) (@lem45286 A B _1243 _1244 _1242 a b h1)). Qed.
Lemma lem45389 (b : Prop) (a : Prop) : (a \/ b) = (term304 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem45390 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) : (term301 A B _1242 _1243 _1244) = (term305 A B _1243 _1244 _1242).
Proof. exact (@lem45389 (term51 A B _1242 _1243 _1244) ((term15 A B _1242) = _1242)). Qed.
Lemma lem45392 (a : Prop) : (term306 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem45393 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : (term307 A B _1242 _1243 _1244) = (_1242 = (@mk_pair A B _1243 _1244)).
Proof. exact (@lem45392 (_1242 = (@mk_pair A B _1243 _1244))). Qed.
Lemma lem45394 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem45395 {A B : Type'} (_1242 : type1413 A B) (_1243 : A) (_1244 : B) : (term308 A B _1242 _1243 _1244) = (term309 A B _1242 _1243 _1244).
Proof. exact (MK_COMB (@lem45394) (@lem45393 A B _1242 _1243 _1244)). Qed.
Lemma lem45396 {A B : Type'} (_1242 : type1413 A B) : ((term15 A B _1242) = _1242) = ((term15 A B _1242) = _1242).
Proof. exact (eq_refl ((term15 A B _1242) = _1242)). Qed.
Lemma lem45397 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) : (term305 A B _1243 _1244 _1242) = (term310 A B _1243 _1244 _1242).
Proof. exact (MK_COMB (@lem45395 A B _1242 _1243 _1244) (@lem45396 A B _1242)). Qed.
Lemma lem45398 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) : (term301 A B _1242 _1243 _1244) = (term310 A B _1243 _1244 _1242).
Proof. exact (TRANS (@lem45390 A B _1243 _1244 _1242) (@lem45397 A B _1243 _1244 _1242)). Qed.
Lemma lem45401 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term310 A B _1243 _1244 _1242.
Proof. exact (EQ_MP (@lem45398 A B _1243 _1244 _1242) (@lem45387 A B _1242 _1243 _1244 a b h1)). Qed.
Lemma lem45402 {A B : Type'} (_1243 : A) (_1244 : B) (_1242 : type1413 A B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term310 A B _1243 _1244 _1242.
Proof. exact (@lem45401 A B _1243 _1244 _1242 a b h1). Qed.
Lemma lem45403 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term311 A B x y.
Proof. exact (@lem45402 A B x y (@mk_pair A B x y) a b h1). Qed.
Lemma lem45406 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : (term25 A B x y) = (@mk_pair A B x y).
Proof. exact (@lem45403 A B x y a b h1 (@lem45350 A B x y)). Qed.
Lemma lem45407 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : (term25 A B x y) = (@mk_pair A B x y).
Proof. exact (@lem45406 A B x y a b h1). Qed.
Lemma lem45408 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : term312 A B x y.
Proof. exact (fun h0 : term35 A B x y => @lem45407 A B x y a b h1). Qed.
Lemma lem45410 (p : Prop) : (term300 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem45411 {A B : Type'} (x : A) (y : B) : (term312 A B x y) = ((term25 A B x y) = (@mk_pair A B x y)).
Proof. exact (@lem45410 ((term25 A B x y) = (@mk_pair A B x y))). Qed.
Lemma lem45412 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term253 A B a b) : (term25 A B x y) = (@mk_pair A B x y).
Proof. exact (EQ_MP (@lem45411 A B x y) (@lem45408 A B x y a b h1)). Qed.
Lemma lem45415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem45417 {A B : Type'} (x : A) (y : B) : (term35 A B x y) = (term313 A B x y).
Proof. exact (@lem45415 ((term25 A B x y) = (@mk_pair A B x y))). Qed.
Lemma lem45420 {A B : Type'} (x : A) (y : B) (h1 : term35 A B x y) : term313 A B x y.
Proof. exact (EQ_MP (@lem45417 A B x y) (@lem45272 A B x y h1)). Qed.
Lemma lem45423 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (@lem45420 A B x y h1 (@lem45412 A B x y a b h2)). Qed.
Lemma lem45424 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : term314.
Proof. exact (fun h0 : ~ False => @lem45423 A B x y a b h1 h2). Qed.
Lemma lem45426 (p : Prop) : (term300 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem45427 : term314 = False.
Proof. exact (@lem45426 False). Qed.
Lemma lem45428 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (EQ_MP (@lem45427) (@lem45424 A B x y a b h1 h2)). Qed.
Lemma lem45429 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : (term35 A B x y) = False.
Proof. exact (prop_ext (fun h3 : term35 A B x y => @lem45428 A B x y a b h1 h2) (fun h3 : False => @lem45272 A B x y h1)). Qed.
Lemma lem45430 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (EQ_MP (@lem45429 A B x y a b h1 h2) (@lem45272 A B x y h1)). Qed.
Lemma lem45431 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : (term35 A B x y) = False.
Proof. exact (prop_ext (fun h3 : term35 A B x y => @lem45430 A B x y a b h1 h2) (fun h3 : False => @lem45162 A B x y h1)). Qed.
Lemma lem45432 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (EQ_MP (@lem45431 A B x y a b h1 h2) (@lem45162 A B x y h1)). Qed.
Lemma lem45433 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : (term35 A B x y) = False.
Proof. exact (prop_ext (fun h3 : term35 A B x y => @lem45432 A B x y a b h1 h2) (fun h3 : False => @lem45162 A B x y h1)). Qed.
Lemma lem45434 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (EQ_MP (@lem45433 A B x y a b h1 h2) (@lem45162 A B x y h1)). Qed.
Lemma lem45435 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : (term35 A B x y) = False.
Proof. exact (prop_ext (fun h3 : term35 A B x y => @lem45434 A B x y a b h1 h2) (fun h3 : False => @lem45154 A B x y h1)). Qed.
Lemma lem45436 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (EQ_MP (@lem45435 A B x y a b h1 h2) (@lem45154 A B x y h1)). Qed.
Lemma lem45437 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : (term253 A B a b) = False.
Proof. exact (prop_ext (fun h3 : term253 A B a b => @lem45436 A B x y a b h1 h2) (fun h3 : False => @lem45134 A B a b h2)). Qed.
Lemma lem45438 {A B : Type'} (x : A) (y : B) (a : type473 A B) (b : type474 A B) (h1 : term35 A B x y) (h2 : term253 A B a b) : False.
Proof. exact (EQ_MP (@lem45437 A B x y a b h1 h2) (@lem45134 A B a b h2)). Qed.
Lemma lem45439 {A B : Type'} (x : A) (a : type473 A B) (b : type474 A B) (h1 : term38 A B x) (h2 : term253 A B a b) : False.
Proof. exact (ex_elim (@lem45052 A B x h1) (fun y : B => fun h0 : term37 A B x y => @lem45438 A B x y a b h0 h2)). Qed.
Lemma lem45440 {A B : Type'} (a : type473 A B) (b : type474 A B) (h1 : term6 A B) (h2 : term253 A B a b) : False.
Proof. exact (ex_elim (@lem44626 A B h1) (fun x : A => fun h0 : term43 A B x => @lem45439 A B x a b h0 h2)). Qed.
Lemma lem45441 {A B : Type'} (a : type473 A B) (h1 : term256 A B a) (h2 : term6 A B) : False.
Proof. exact (ex_elim (@lem45050 A B a h1) (fun b : type474 A B => fun h0 : term255 A B a b => @lem45440 A B a b h2 h0)). Qed.
Lemma lem45442 {A B : Type'} (h1 : term6 A B) (h2 : term2 A B) : False.
Proof. exact (ex_elim (@lem45049 A B h2) (fun a : type473 A B => fun h0 : term257 A B a => @lem45441 A B a h0 h1)). Qed.
Lemma lem45443 {A B : Type'} (h1 : term6 A B) : term11 A B.
Proof. exact (fun h0 : term2 A B => @lem45442 A B h1 h0). Qed.
Lemma lem45444 {A B : Type'} : (term11 A B) = (term12 A B).
Proof. exact (@lem69 (term2 A B)). Qed.
Lemma lem45445 {A B : Type'} (h1 : term6 A B) : term12 A B.
Proof. exact (EQ_MP (@lem45444 A B) (@lem45443 A B h1)). Qed.
Lemma lem45446 {A B : Type'} : term14 A B.
Proof. exact (fun h0 : term6 A B => @lem45445 A B h0). Qed.
Lemma lem45447 {A B : Type'} : term7 A B.
Proof. exact (EQ_MP (@lem44590 A B) (@lem45446 A B)). Qed.
Lemma lem45449 {A B : Type'} : term7 A B.
Proof. exact (@lem44472 A B (@lem45447 A B)). Qed.
Lemma lem45450 {A B : Type'} (h1 : term6 A B) : term11 A B.
Proof. exact (@lem45449 A B (@lem44452 A B h1)). Qed.
Lemma lem45451 {A B : Type'} (h1 : term6 A B) : False.
Proof. exact (@lem45450 A B h1 (@lem44453 A B)). Qed.
Lemma lem45452 {A B : Type'} (h1 : term6 A B) : (term6 A B) = False.
Proof. exact (prop_ext (fun h2 : term6 A B => @lem45451 A B h1) (fun h2 : False => @lem44452 A B h1)). Qed.
Lemma lem45453 {A B : Type'} (h1 : term6 A B) : False.
Proof. exact (EQ_MP (@lem45452 A B h1) (@lem44452 A B h1)). Qed.
Lemma lem45454 {A B : Type'} : term5 A B.
Proof. exact (fun h0 : term6 A B => @lem45453 A B h0). Qed.
Lemma lem45455 {A B : Type'} : term4 A B.
Proof. exact (EQ_MP (@lem44451 A B) (@lem45454 A B)). Qed.
