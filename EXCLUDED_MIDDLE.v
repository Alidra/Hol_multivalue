Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXCLUDED_MIDDLE_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm37_spec.
Require Import thm43_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm9425_spec.
Lemma lem9548 (h1 : True = False) : True = False.
Proof. exact (h1). Qed.
Lemma lem9549 : term0.
Proof. exact (@lem43 False True). Qed.
Lemma lem9551 : term1.
Proof. exact (@lem37 True False). Qed.
Lemma lem9554 (h1 : True = False) : False -> True.
Proof. exact (@lem9549 (@lem9548 h1)). Qed.
Lemma lem9555 (h1 : True = False) : True -> False.
Proof. exact (@lem9551 (@lem9548 h1)). Qed.
Lemma lem9557 (h1 : True -> False) : True -> False.
Proof. exact (h1). Qed.
Lemma lem9558 (h1 : True) : True.
Proof. exact (h1). Qed.
Lemma lem9559 (h1 : True) (h2 : True -> False) : False.
Proof. exact (@lem9557 h2 (@lem9558 h1)). Qed.
Lemma lem9560 (h1 : True -> False) : True = False.
Proof. exact (prop_ext (fun h2 : True => @lem9559 h2 h1) (fun h2 : False => @lem0)). Qed.
Lemma lem9561 (h1 : True -> False) : False.
Proof. exact (EQ_MP (@lem9560 h1) (@lem0)). Qed.
Lemma lem9562 : term2.
Proof. exact (fun h0 : True -> False => @lem9561 h0). Qed.
Lemma lem9563 : term3.
Proof. exact (fun h0 : False -> True => @lem9562). Qed.
Lemma lem9564 (h1 : True = False) : term2.
Proof. exact (@lem9563 (@lem9554 h1)). Qed.
Lemma lem9565 (h1 : True = False) : False.
Proof. exact (@lem9564 h1 (@lem9555 h1)). Qed.
Lemma lem9566 : term4.
Proof. exact (fun h0 : True = False => @lem9565 h0). Qed.
Lemma lem9567 : term4 = term5.
Proof. exact (@lem69 (True = False)). Qed.
Lemma lem9568 : term5.
Proof. exact (EQ_MP (@lem9567) (@lem9566)). Qed.
Lemma lem9569 (t : Prop) (h1 : term6 t) : term6 t.
Proof. exact (h1). Qed.
Lemma lem9570 (P : Prop -> Prop) : (term7 P) = (ex P).
Proof. exact (@lem9425 Prop P). Qed.
Lemma lem9571 (t : Prop) : (term8 t) = (term9 t).
Proof. exact (@lem9570 (term10 t)). Qed.
Lemma lem9572 (t : Prop) : (term8 t) = (term11 t).
Proof. exact (eq_refl (term8 t)). Qed.
Lemma lem9573 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9574 (t : Prop) : (term12 t) = (term13 t).
Proof. exact (MK_COMB (@lem9573) (@lem9572 t)). Qed.
Lemma lem9575 (t : Prop) : (term9 t) = (term9 t).
Proof. exact (eq_refl (term9 t)). Qed.
Lemma lem9576 (t : Prop) : ((term8 t) = (term9 t)) = ((term11 t) = (term9 t)).
Proof. exact (MK_COMB (@lem9574 t) (@lem9575 t)). Qed.
Lemma lem9577 (t : Prop) : (term11 t) = (term9 t).
Proof. exact (EQ_MP (@lem9576 t) (@lem9571 t)). Qed.
Lemma lem9578 (t : Prop) : (term9 t) = (term11 t).
Proof. exact (SYM (@lem9577 t)). Qed.
Lemma lem9579 (P : Prop -> Prop) : (term7 P) = (ex P).
Proof. exact (@lem9425 Prop P). Qed.
Lemma lem9580 (t : Prop) : (term14 t) = (term15 t).
Proof. exact (@lem9579 (term16 t)). Qed.
Lemma lem9581 (t : Prop) : (term14 t) = (term17 t).
Proof. exact (eq_refl (term14 t)). Qed.
Lemma lem9582 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9583 (t : Prop) : (term18 t) = (term19 t).
Proof. exact (MK_COMB (@lem9582) (@lem9581 t)). Qed.
Lemma lem9584 (t : Prop) : (term15 t) = (term15 t).
Proof. exact (eq_refl (term15 t)). Qed.
Lemma lem9585 (t : Prop) : ((term14 t) = (term15 t)) = ((term17 t) = (term15 t)).
Proof. exact (MK_COMB (@lem9583 t) (@lem9584 t)). Qed.
Lemma lem9586 (t : Prop) : (term17 t) = (term15 t).
Proof. exact (EQ_MP (@lem9585 t) (@lem9580 t)). Qed.
Lemma lem9587 (t : Prop) : (term15 t) = (term17 t).
Proof. exact (SYM (@lem9586 t)). Qed.
Lemma lem9588 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem9589 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem9590 (t : Prop) : term20 t.
Proof. exact (or_intro1 (@lem9589) t). Qed.
Lemma lem9591 (t : Prop) : term21 t.
Proof. exact (or_intro1 (@lem9588) t). Qed.
Lemma lem9592 (t : Prop) : term15 t.
Proof. exact (ex_intro (term16 t) True (@lem9590 t)). Qed.
Lemma lem9593 (t : Prop) : term9 t.
Proof. exact (ex_intro (term10 t) False (@lem9591 t)). Qed.
Lemma lem9594 (t : Prop) : term17 t.
Proof. exact (EQ_MP (@lem9587 t) (@lem9592 t)). Qed.
Lemma lem9595 (t : Prop) : term11 t.
Proof. exact (EQ_MP (@lem9578 t) (@lem9593 t)). Qed.
Lemma lem9596 (t : Prop) : term6 t.
Proof. exact (conj (@lem9595 t) (@lem9594 t)). Qed.
Lemma lem9597 (t : Prop) (h1 : term6 t) : term6 t.
Proof. exact (h1). Qed.
Lemma lem9600 (t : Prop) (h1 : (term22 t) = False) : (term22 t) = False.
Proof. exact (h1). Qed.
Lemma lem9601 (t : Prop) (h1 : (term22 t) = False) : False = (term22 t).
Proof. exact (SYM (@lem9600 t h1)). Qed.
Lemma lem9602 (t : Prop) (h1 : False = (term22 t)) : False = (term22 t).
Proof. exact (h1). Qed.
Lemma lem9603 (t : Prop) (h1 : False = (term22 t)) : (term22 t) = False.
Proof. exact (SYM (@lem9602 t h1)). Qed.
Lemma lem9604 (t : Prop) : ((term22 t) = False) = (False = (term22 t)).
Proof. exact (prop_ext (fun h1 : (term22 t) = False => @lem9601 t h1) (fun h1 : False = (term22 t) => @lem9603 t h1)). Qed.
Lemma lem9605 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9606 (t : Prop) : (term23 t) = (term24 t).
Proof. exact (MK_COMB (@lem9605) (@lem9604 t)). Qed.
Lemma lem9608 (t : Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem9609 (t : Prop) : (term11 t) = (term25 t).
Proof. exact (MK_COMB (@lem9606 t) (@lem9608 t)). Qed.
Lemma lem9610 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem9611 (t : Prop) : (term26 t) = (term27 t).
Proof. exact (MK_COMB (@lem9610) (@lem9609 t)). Qed.
Lemma lem9613 (t : Prop) (h1 : (term28 t) = True) : (term28 t) = True.
Proof. exact (h1). Qed.
Lemma lem9614 (t : Prop) (h1 : (term28 t) = True) : True = (term28 t).
Proof. exact (SYM (@lem9613 t h1)). Qed.
Lemma lem9615 (t : Prop) (h1 : True = (term28 t)) : True = (term28 t).
Proof. exact (h1). Qed.
Lemma lem9616 (t : Prop) (h1 : True = (term28 t)) : (term28 t) = True.
Proof. exact (SYM (@lem9615 t h1)). Qed.
Lemma lem9617 (t : Prop) : ((term28 t) = True) = (True = (term28 t)).
Proof. exact (prop_ext (fun h1 : (term28 t) = True => @lem9614 t h1) (fun h1 : True = (term28 t) => @lem9616 t h1)). Qed.
Lemma lem9618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9619 (t : Prop) : (term29 t) = (term30 t).
Proof. exact (MK_COMB (@lem9618) (@lem9617 t)). Qed.
Lemma lem9621 (t : Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem9622 (t : Prop) : (term17 t) = (term31 t).
Proof. exact (MK_COMB (@lem9619 t) (@lem9621 t)). Qed.
Lemma lem9623 (t : Prop) : (term6 t) = (term32 t).
Proof. exact (MK_COMB (@lem9611 t) (@lem9622 t)). Qed.
Lemma lem9624 (t : Prop) (h1 : term6 t) : term32 t.
Proof. exact (EQ_MP (@lem9623 t) (@lem9597 t h1)). Qed.
Lemma lem9625 (t : Prop) (h1 : term31 t) : term31 t.
Proof. exact (h1). Qed.
Lemma lem9626 (t : Prop) (h1 : True = (term28 t)) : True = (term28 t).
Proof. exact (h1). Qed.
Lemma lem9627 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem9628 (t : Prop) (h1 : term25 t) : term25 t.
Proof. exact (h1). Qed.
Lemma lem9629 (t : Prop) (h1 : False = (term22 t)) : False = (term22 t).
Proof. exact (h1). Qed.
Lemma lem9630 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem9631 (t : Prop) (h1 : t) : term33 t.
Proof. exact (or_intro1 (@lem9627 t h1) (~ t)). Qed.
Lemma lem9632 (t : Prop) (h1 : t) : term33 t.
Proof. exact (or_intro1 (@lem9630 t h1) (~ t)). Qed.
Lemma lem9633 (t : Prop) (h1 : t) : term33 t.
Proof. exact (or_intro1 (@lem9630 t h1) (~ t)). Qed.
Lemma lem9634 (t : Prop) (h1 : t) : t.
Proof. exact (h1). Qed.
Lemma lem9638 (t : Prop) (h1 : True = (term28 t)) : True = (term28 t).
Proof. exact (h1). Qed.
Lemma lem9639 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9640 (t : Prop) (h1 : True = (term28 t)) : (@eq Prop True) = (term34 t).
Proof. exact (MK_COMB (@lem9639) (@lem9638 t h1)). Qed.
Lemma lem9642 (t : Prop) (h1 : False = (term22 t)) : False = (term22 t).
Proof. exact (h1). Qed.
Lemma lem9643 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : (True = False) = ((term28 t) = (term22 t)).
Proof. exact (MK_COMB (@lem9640 t h2) (@lem9642 t h1)). Qed.
Lemma lem9644 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem9645 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : term5 = (term35 t).
Proof. exact (MK_COMB (@lem9644) (@lem9643 t h1 h2)). Qed.
Lemma lem9646 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem9647 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : term36 = (term37 t).
Proof. exact (MK_COMB (@lem9646) (@lem9645 t h1 h2)). Qed.
Lemma lem9649 (t : Prop) (h1 : False = (term22 t)) : False = (term22 t).
Proof. exact (h1). Qed.
Lemma lem9650 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : term38 = (term39 t).
Proof. exact (MK_COMB (@lem9647 t h1 h2) (@lem9649 t h1)). Qed.
Lemma lem9651 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : (term39 t) = term38.
Proof. exact (SYM (@lem9650 t h1 h2)). Qed.
Lemma lem9652 (t : Prop) : t = (t = True).
Proof. exact (@lem7 t). Qed.
Lemma lem9665 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem9666 (x : Prop) : (x = True) = x.
Proof. exact (@lem9665 x). Qed.
Lemma lem9667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9668 (x : Prop) : (term40 x) = (or x).
Proof. exact (MK_COMB (@lem9667) (@lem9666 x)). Qed.
Lemma lem9670 (t : Prop) (h1 : t) : t = True.
Proof. exact (EQ_MP (@lem9652 t) (@lem9634 t h1)). Qed.
Lemma lem9673 (x : Prop) (t : Prop) (h1 : t) : (term41 x t) = (x \/ True).
Proof. exact (MK_COMB (@lem9668 x) (@lem9670 t h1)). Qed.
Lemma lem9675 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem9676 (x : Prop) : (x \/ True) = True.
Proof. exact (@lem9675 x). Qed.
Lemma lem9679 (x : Prop) (t : Prop) (h1 : t) : (term41 x t) = True.
Proof. exact (TRANS (@lem9673 x t h1) (@lem9676 x)). Qed.
Lemma lem9680 (t : Prop) (h1 : t) : (term16 t) = term42.
Proof. exact (fun_ext (fun x : Prop => @lem9679 x t h1)). Qed.
Lemma lem9681 : (@ε Prop) = (@ε Prop).
Proof. exact (eq_refl (@ε Prop)). Qed.
Lemma lem9682 (t : Prop) (h1 : t) : (term28 t) = term43.
Proof. exact (MK_COMB (@lem9681) (@lem9680 t h1)). Qed.
Lemma lem9683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem9684 (t : Prop) (h1 : t) : (term34 t) = term44.
Proof. exact (MK_COMB (@lem9683) (@lem9682 t h1)). Qed.
Lemma lem9688 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem9689 (x : Prop) : (x = False) = (~ x).
Proof. exact (@lem9688 x). Qed.
Lemma lem9690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9691 (x : Prop) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem9690) (@lem9689 x)). Qed.
Lemma lem9693 (t : Prop) (h1 : t) : t = True.
Proof. exact (EQ_MP (@lem9652 t) (@lem9634 t h1)). Qed.
Lemma lem9696 (x : Prop) (t : Prop) (h1 : t) : (term47 x t) = (term48 x).
Proof. exact (MK_COMB (@lem9691 x) (@lem9693 t h1)). Qed.
Lemma lem9698 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem9699 (x : Prop) : (term48 x) = True.
Proof. exact (@lem9698 (~ x)). Qed.
Lemma lem9702 (x : Prop) (t : Prop) (h1 : t) : (term47 x t) = True.
Proof. exact (TRANS (@lem9696 x t h1) (@lem9699 x)). Qed.
Lemma lem9703 (t : Prop) (h1 : t) : (term10 t) = term42.
Proof. exact (fun_ext (fun x : Prop => @lem9702 x t h1)). Qed.
Lemma lem9704 : (@ε Prop) = (@ε Prop).
Proof. exact (eq_refl (@ε Prop)). Qed.
Lemma lem9705 (t : Prop) (h1 : t) : (term22 t) = term43.
Proof. exact (MK_COMB (@lem9704) (@lem9703 t h1)). Qed.
Lemma lem9706 (t : Prop) (h1 : t) : ((term28 t) = (term22 t)) = (term43 = term43).
Proof. exact (MK_COMB (@lem9684 t h1) (@lem9705 t h1)). Qed.
Lemma lem9708 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem9709 (x : Prop) : (x = x) = True.
Proof. exact (@lem9708 Prop x). Qed.
Lemma lem9710 : (term43 = term43) = True.
Proof. exact (@lem9709 term43). Qed.
Lemma lem9713 (t : Prop) (h1 : t) : ((term28 t) = (term22 t)) = True.
Proof. exact (TRANS (@lem9706 t h1) (@lem9710)). Qed.
Lemma lem9714 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem9715 (t : Prop) (h1 : t) : (term35 t) = (~ True).
Proof. exact (MK_COMB (@lem9714) (@lem9713 t h1)). Qed.
Lemma lem9717 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem9720 (t : Prop) (h1 : t) : (term35 t) = False.
Proof. exact (TRANS (@lem9715 t h1) (@lem9717)). Qed.
Lemma lem9721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem9722 (t : Prop) (h1 : t) : (term37 t) = (imp False).
Proof. exact (MK_COMB (@lem9721) (@lem9720 t h1)). Qed.
Lemma lem9726 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem9727 (x : Prop) : (x = False) = (~ x).
Proof. exact (@lem9726 x). Qed.
Lemma lem9728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem9729 (x : Prop) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem9728) (@lem9727 x)). Qed.
Lemma lem9731 (t : Prop) (h1 : t) : t = True.
Proof. exact (EQ_MP (@lem9652 t) (@lem9634 t h1)). Qed.
Lemma lem9734 (x : Prop) (t : Prop) (h1 : t) : (term47 x t) = (term48 x).
Proof. exact (MK_COMB (@lem9729 x) (@lem9731 t h1)). Qed.
Lemma lem9736 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem9737 (x : Prop) : (term48 x) = True.
Proof. exact (@lem9736 (~ x)). Qed.
Lemma lem9740 (x : Prop) (t : Prop) (h1 : t) : (term47 x t) = True.
Proof. exact (TRANS (@lem9734 x t h1) (@lem9737 x)). Qed.
Lemma lem9741 (t : Prop) (h1 : t) : (term10 t) = term42.
Proof. exact (fun_ext (fun x : Prop => @lem9740 x t h1)). Qed.
Lemma lem9742 : (@ε Prop) = (@ε Prop).
Proof. exact (eq_refl (@ε Prop)). Qed.
Lemma lem9743 (t : Prop) (h1 : t) : (term22 t) = term43.
Proof. exact (MK_COMB (@lem9742) (@lem9741 t h1)). Qed.
Lemma lem9744 (t : Prop) (h1 : t) : (term39 t) = term49.
Proof. exact (MK_COMB (@lem9722 t h1) (@lem9743 t h1)). Qed.
Lemma lem9746 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem9747 : term49 = True.
Proof. exact (@lem9746 term43). Qed.
Lemma lem9750 (t : Prop) (h1 : t) : (term39 t) = True.
Proof. exact (TRANS (@lem9744 t h1) (@lem9747)). Qed.
Lemma lem9751 (t : Prop) (h1 : t) : True = (term39 t).
Proof. exact (SYM (@lem9750 t h1)). Qed.
Lemma lem9752 (t : Prop) (h1 : t) : term39 t.
Proof. exact (EQ_MP (@lem9751 t h1) (@lem0)). Qed.
Lemma lem9753 (t : Prop) (h1 : t) (h2 : False = (term22 t)) (h3 : True = (term28 t)) : term38.
Proof. exact (EQ_MP (@lem9651 t h2 h3) (@lem9752 t h1)). Qed.
Lemma lem9754 (t : Prop) (h1 : t) (h2 : False = (term22 t)) (h3 : True = (term28 t)) : False.
Proof. exact (@lem9753 t h1 h2 h3 (@lem9568)). Qed.
Lemma lem9755 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : t -> False.
Proof. exact (fun h0 : t => @lem9754 t h0 h1 h2). Qed.
Lemma lem9756 (t : Prop) : (t -> False) = (~ t).
Proof. exact (@lem69 t). Qed.
Lemma lem9757 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : ~ t.
Proof. exact (EQ_MP (@lem9756 t) (@lem9755 t h1 h2)). Qed.
Lemma lem9758 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : term33 t.
Proof. exact (or_intro2 t (@lem9757 t h1 h2)). Qed.
Lemma lem9759 (t : Prop) (h1 : term6 t) : term31 t.
Proof. exact (proj2 (@lem9624 t h1)). Qed.
Lemma lem9760 (t : Prop) (h1 : term6 t) : term25 t.
Proof. exact (proj1 (@lem9624 t h1)). Qed.
Lemma lem9761 (t : Prop) (h1 : t) (h2 : term31 t) : term33 t.
Proof. exact (or_elim (@lem9625 t h2) (fun h0 : True = (term28 t) => @lem9632 t h1) (fun h0 : t => @lem9633 t h1)). Qed.
Lemma lem9762 (t : Prop) (h1 : t) : t = (term33 t).
Proof. exact (prop_ext (fun h2 : t => @lem9631 t h1) (fun h2 : term33 t => @lem9627 t h1)). Qed.
Lemma lem9763 (t : Prop) (h1 : t) : term33 t.
Proof. exact (EQ_MP (@lem9762 t h1) (@lem9627 t h1)). Qed.
Lemma lem9764 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : (True = (term28 t)) = (term33 t).
Proof. exact (prop_ext (fun h3 : True = (term28 t) => @lem9758 t h1 h2) (fun h3 : term33 t => @lem9626 t h2)). Qed.
Lemma lem9765 (t : Prop) (h1 : False = (term22 t)) (h2 : True = (term28 t)) : term33 t.
Proof. exact (EQ_MP (@lem9764 t h1 h2) (@lem9626 t h2)). Qed.
Lemma lem9766 (t : Prop) (h1 : False = (term22 t)) (h2 : term31 t) : term33 t.
Proof. exact (or_elim (@lem9625 t h2) (fun h0 : True = (term28 t) => @lem9765 t h1 h0) (fun h0 : t => @lem9763 t h0)). Qed.
Lemma lem9767 (t : Prop) (h1 : t) (h2 : term31 t) : t = (term33 t).
Proof. exact (prop_ext (fun h3 : t => @lem9761 t h1 h2) (fun h3 : term33 t => @lem9630 t h1)). Qed.
Lemma lem9768 (t : Prop) (h1 : t) (h2 : term31 t) : term33 t.
Proof. exact (EQ_MP (@lem9767 t h1 h2) (@lem9630 t h1)). Qed.
Lemma lem9769 (t : Prop) (h1 : False = (term22 t)) (h2 : term31 t) : (False = (term22 t)) = (term33 t).
Proof. exact (prop_ext (fun h3 : False = (term22 t) => @lem9766 t h1 h2) (fun h3 : term33 t => @lem9629 t h1)). Qed.
Lemma lem9770 (t : Prop) (h1 : False = (term22 t)) (h2 : term31 t) : term33 t.
Proof. exact (EQ_MP (@lem9769 t h1 h2) (@lem9629 t h1)). Qed.
Lemma lem9771 (t : Prop) (h1 : term25 t) (h2 : term31 t) : term33 t.
Proof. exact (or_elim (@lem9628 t h1) (fun h0 : False = (term22 t) => @lem9770 t h0 h2) (fun h0 : t => @lem9768 t h0 h2)). Qed.
Lemma lem9772 (t : Prop) (h1 : term6 t) (h2 : term25 t) : (term31 t) = (term33 t).
Proof. exact (prop_ext (fun h3 : term31 t => @lem9771 t h2 h3) (fun h3 : term33 t => @lem9759 t h1)). Qed.
Lemma lem9773 (t : Prop) (h1 : term6 t) (h2 : term25 t) : term33 t.
Proof. exact (EQ_MP (@lem9772 t h1 h2) (@lem9759 t h1)). Qed.
Lemma lem9774 (t : Prop) (h1 : term6 t) : (term25 t) = (term33 t).
Proof. exact (prop_ext (fun h2 : term25 t => @lem9773 t h1 h2) (fun h2 : term33 t => @lem9760 t h1)). Qed.
Lemma lem9775 (t : Prop) (h1 : term6 t) : term33 t.
Proof. exact (EQ_MP (@lem9774 t h1) (@lem9760 t h1)). Qed.
Lemma lem9776 (t : Prop) : term50 t.
Proof. exact (fun h0 : term6 t => @lem9775 t h0). Qed.
Lemma lem9777 (t : Prop) (h1 : term6 t) : term33 t.
Proof. exact (@lem9776 t (@lem9569 t h1)). Qed.
Lemma lem9778 (t : Prop) : (term6 t) = (term33 t).
Proof. exact (prop_ext (fun h1 : term6 t => @lem9777 t h1) (fun h1 : term33 t => @lem9596 t)). Qed.
Lemma lem9779 (t : Prop) : term33 t.
Proof. exact (EQ_MP (@lem9778 t) (@lem9596 t)). Qed.
Lemma lem9784 : term51.
Proof. exact (fun t : Prop => @lem9779 t). Qed.
