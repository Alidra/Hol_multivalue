Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_UNION_EQ_term_abbrevs.
Require Import CARD_UNION_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_spec.
Require Import SUBSET_UNION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm69_spec.
Lemma lem3845384 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3845385 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3845386 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3845385 t1) (@lem3845384 t1)). Qed.
Lemma lem3845387 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3845386 t1 t2). Qed.
Lemma lem3845388 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3845389 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3845388 t1 t2) (@lem3845387 t1 t2)). Qed.
Lemma lem3845390 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3845389 t1 t2 t3). Qed.
Lemma lem3845391 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3845392 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3845391 t1 t2 t3) (@lem3845390 t1 t2 t3)). Qed.
Lemma lem3845393 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3845392 t1 t2 t3)). Qed.
Lemma lem3845395 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3845396 {_99816 : Type'} : (term8 _99816) = (term9 _99816).
Proof. exact (@lem3845395 (term8 _99816)). Qed.
Lemma lem3845397 {_99816 : Type'} : (term9 _99816) = (term8 _99816).
Proof. exact (SYM (@lem3845396 _99816)). Qed.
Lemma lem3845398 {_99816 : Type'} (h1 : term10 _99816) : term10 _99816.
Proof. exact (h1). Qed.
Lemma lem3845399 {_99816 : Type'} : term11 _99816.
Proof. exact (@lem3843862 _99816). Qed.
Lemma lem3845405 {_99816 : Type'} : term12 _99816.
Proof. exact (@lem3599924 _99816). Qed.
Lemma lem3845406 {A : Type'} : term12 A.
Proof. exact (@lem3599924 A). Qed.
Lemma lem3845407 {A : Type'} : term13 A.
Proof. exact (@lem3234183 A). Qed.
Lemma lem3845408 {_99816 : Type'} : term13 _99816.
Proof. exact (@lem3234183 _99816). Qed.
Lemma lem3845413 {_99816 A : Type'} (h1 : term14 _99816 A) : term14 _99816 A.
Proof. exact (h1). Qed.
Lemma lem3845414 {_99816 A : Type'} : term15 _99816 A.
Proof. exact (fun h0 : term14 _99816 A => @lem3845413 _99816 A h0). Qed.
Lemma lem3845415 {_99816 A : Type'} (h1 : term15 _99816 A) : term15 _99816 A.
Proof. exact (h1). Qed.
Lemma lem3845416 {_99816 A : Type'} (h1 : term14 _99816 A) : term14 _99816 A.
Proof. exact (h1). Qed.
Lemma lem3845417 {_99816 A : Type'} (h1 : term14 _99816 A) (h2 : term15 _99816 A) : term14 _99816 A.
Proof. exact (@lem3845415 _99816 A h2 (@lem3845416 _99816 A h1)). Qed.
Lemma lem3845418 {_99816 A : Type'} (h1 : term14 _99816 A) : term16 _99816 A.
Proof. exact (fun h0 : term15 _99816 A => @lem3845417 _99816 A h1 h0). Qed.
Lemma lem3845419 {_99816 A : Type'} (h1 : term15 _99816 A) : term15 _99816 A.
Proof. exact (h1). Qed.
Lemma lem3845420 {_99816 A : Type'} (h1 : term14 _99816 A) (h2 : term15 _99816 A) : term14 _99816 A.
Proof. exact (@lem3845418 _99816 A h1 (@lem3845419 _99816 A h2)). Qed.
Lemma lem3845421 {_99816 A : Type'} (h1 : term15 _99816 A) : term15 _99816 A.
Proof. exact (fun h0 : term14 _99816 A => @lem3845420 _99816 A h0 h1). Qed.
Lemma lem3845422 {_99816 A : Type'} : term17 _99816 A.
Proof. exact (fun h0 : term15 _99816 A => @lem3845421 _99816 A h0). Qed.
Lemma lem3845425 {_99816 A : Type'} : term15 _99816 A.
Proof. exact (@lem3845422 _99816 A (@lem3845414 _99816 A)). Qed.
Lemma lem3845426 {_99816 A : Type'} : term15 _99816 A.
Proof. exact (@lem3845425 _99816 A). Qed.
Lemma lem3845532 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3845533 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (@lem3845532 (term11 A)). Qed.
Lemma lem3845548 {_99816 : Type'} : (term20 _99816) = (term20 _99816).
Proof. exact (eq_refl (term20 _99816)). Qed.
Lemma lem3845549 {_99816 A : Type'} : (term21 _99816 A) = (term22 _99816 A).
Proof. exact (MK_COMB (@lem3845548 _99816) (@lem3845533 A)). Qed.
Lemma lem3845552 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (eq_refl (term23 A)). Qed.
Lemma lem3845553 {_99816 A : Type'} : (term24 _99816 A) = (term25 _99816 A).
Proof. exact (MK_COMB (@lem3845552 A) (@lem3845549 _99816 A)). Qed.
Lemma lem3845556 {_99816 : Type'} : (term23 _99816) = (term23 _99816).
Proof. exact (eq_refl (term23 _99816)). Qed.
Lemma lem3845557 {_99816 A : Type'} : (term26 _99816 A) = (term27 _99816 A).
Proof. exact (MK_COMB (@lem3845556 _99816) (@lem3845553 _99816 A)). Qed.
Lemma lem3845560 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (eq_refl (term28 A)). Qed.
Lemma lem3845561 {_99816 A : Type'} : (term29 _99816 A) = (term30 _99816 A).
Proof. exact (MK_COMB (@lem3845560 A) (@lem3845557 _99816 A)). Qed.
Lemma lem3845564 {_99816 : Type'} : (term28 _99816) = (term28 _99816).
Proof. exact (eq_refl (term28 _99816)). Qed.
Lemma lem3845565 {_99816 A : Type'} : (term31 _99816 A) = (term32 _99816 A).
Proof. exact (MK_COMB (@lem3845564 _99816) (@lem3845561 _99816 A)). Qed.
Lemma lem3845568 {_99816 : Type'} : (term33 _99816) = (term33 _99816).
Proof. exact (eq_refl (term33 _99816)). Qed.
Lemma lem3845575 {_99816 A : Type'} : (term14 _99816 A) = (term34 _99816 A).
Proof. exact (MK_COMB (@lem3845568 _99816) (@lem3845565 _99816 A)). Qed.
Lemma lem3845588 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term35 A s t) = (term35 A s t).
Proof. exact (eq_refl (term35 A s t)). Qed.
Lemma lem3845589 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3845588 A s t)). Qed.
Lemma lem3845590 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845591 {A : Type'} (s : A -> Prop) : (term37 A s) = (term37 A s).
Proof. exact (MK_COMB (@lem3845590 A) (@lem3845589 A s)). Qed.
Lemma lem3845592 {A : Type'} : (term38 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3845591 A s)). Qed.
Lemma lem3845593 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845594 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3845593 A) (@lem3845592 A)). Qed.
Lemma lem3845595 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3845596 {A : Type'} : (term19 A) = (term19 A).
Proof. exact (MK_COMB (@lem3845595) (@lem3845594 A)). Qed.
Lemma lem3845609 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term35 _99816 s t) = (term35 _99816 s t).
Proof. exact (eq_refl (term35 _99816 s t)). Qed.
Lemma lem3845610 {_99816 : Type'} (s : _99816 -> Prop) : (term36 _99816 s) = (term36 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845609 _99816 s t)). Qed.
Lemma lem3845611 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845612 {_99816 : Type'} (s : _99816 -> Prop) : (term37 _99816 s) = (term37 _99816 s).
Proof. exact (MK_COMB (@lem3845611 _99816) (@lem3845610 _99816 s)). Qed.
Lemma lem3845613 {_99816 : Type'} : (term38 _99816) = (term38 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845612 _99816 s)). Qed.
Lemma lem3845614 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845615 {_99816 : Type'} : (term11 _99816) = (term11 _99816).
Proof. exact (MK_COMB (@lem3845614 _99816) (@lem3845613 _99816)). Qed.
Lemma lem3845616 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3845617 {_99816 : Type'} : (term20 _99816) = (term20 _99816).
Proof. exact (MK_COMB (@lem3845616) (@lem3845615 _99816)). Qed.
Lemma lem3845618 {_99816 A : Type'} : (term22 _99816 A) = (term22 _99816 A).
Proof. exact (MK_COMB (@lem3845617 _99816) (@lem3845596 A)). Qed.
Lemma lem3845627 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term39 A t s) = (term39 A t s).
Proof. exact (eq_refl (term39 A t s)). Qed.
Lemma lem3845628 {A : Type'} (s : A -> Prop) : (term40 A s) = (term40 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3845627 A t s)). Qed.
Lemma lem3845629 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845630 {A : Type'} (s : A -> Prop) : (term41 A s) = (term41 A s).
Proof. exact (MK_COMB (@lem3845629 A) (@lem3845628 A s)). Qed.
Lemma lem3845631 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3845630 A s)). Qed.
Lemma lem3845632 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845633 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3845632 A) (@lem3845631 A)). Qed.
Lemma lem3845634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3845635 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3845634) (@lem3845633 A)). Qed.
Lemma lem3845636 {_99816 A : Type'} : (term25 _99816 A) = (term25 _99816 A).
Proof. exact (MK_COMB (@lem3845635 A) (@lem3845618 _99816 A)). Qed.
Lemma lem3845645 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term39 _99816 t s) = (term39 _99816 t s).
Proof. exact (eq_refl (term39 _99816 t s)). Qed.
Lemma lem3845646 {_99816 : Type'} (s : _99816 -> Prop) : (term40 _99816 s) = (term40 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845645 _99816 t s)). Qed.
Lemma lem3845647 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845648 {_99816 : Type'} (s : _99816 -> Prop) : (term41 _99816 s) = (term41 _99816 s).
Proof. exact (MK_COMB (@lem3845647 _99816) (@lem3845646 _99816 s)). Qed.
Lemma lem3845649 {_99816 : Type'} : (term42 _99816) = (term42 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845648 _99816 s)). Qed.
Lemma lem3845650 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845651 {_99816 : Type'} : (term12 _99816) = (term12 _99816).
Proof. exact (MK_COMB (@lem3845650 _99816) (@lem3845649 _99816)). Qed.
Lemma lem3845652 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3845653 {_99816 : Type'} : (term23 _99816) = (term23 _99816).
Proof. exact (MK_COMB (@lem3845652) (@lem3845651 _99816)). Qed.
Lemma lem3845654 {_99816 A : Type'} : (term27 _99816 A) = (term27 _99816 A).
Proof. exact (MK_COMB (@lem3845653 _99816) (@lem3845636 _99816 A)). Qed.
Lemma lem3845655 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term43 A t s) = (term43 A t s).
Proof. exact (eq_refl (term43 A t s)). Qed.
Lemma lem3845656 {A : Type'} (s : A -> Prop) : (term44 A s) = (term44 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3845655 A t s)). Qed.
Lemma lem3845657 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845658 {A : Type'} (s : A -> Prop) : (term45 A s) = (term45 A s).
Proof. exact (MK_COMB (@lem3845657 A) (@lem3845656 A s)). Qed.
Lemma lem3845659 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3845658 A s)). Qed.
Lemma lem3845660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845661 {A : Type'} : (term47 A) = (term47 A).
Proof. exact (MK_COMB (@lem3845660 A) (@lem3845659 A)). Qed.
Lemma lem3845662 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term48 A s t) = (term48 A s t).
Proof. exact (eq_refl (term48 A s t)). Qed.
Lemma lem3845663 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3845662 A s t)). Qed.
Lemma lem3845664 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845665 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem3845664 A) (@lem3845663 A s)). Qed.
Lemma lem3845666 {A : Type'} : (term51 A) = (term51 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3845665 A s)). Qed.
Lemma lem3845667 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3845668 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (MK_COMB (@lem3845667 A) (@lem3845666 A)). Qed.
Lemma lem3845669 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3845670 {A : Type'} : (term53 A) = (term53 A).
Proof. exact (MK_COMB (@lem3845669) (@lem3845668 A)). Qed.
Lemma lem3845671 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem3845670 A) (@lem3845661 A)). Qed.
Lemma lem3845672 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3845673 {A : Type'} : (term28 A) = (term28 A).
Proof. exact (MK_COMB (@lem3845672) (@lem3845671 A)). Qed.
Lemma lem3845674 {_99816 A : Type'} : (term30 _99816 A) = (term30 _99816 A).
Proof. exact (MK_COMB (@lem3845673 A) (@lem3845654 _99816 A)). Qed.
Lemma lem3845675 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term43 _99816 t s) = (term43 _99816 t s).
Proof. exact (eq_refl (term43 _99816 t s)). Qed.
Lemma lem3845676 {_99816 : Type'} (s : _99816 -> Prop) : (term44 _99816 s) = (term44 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845675 _99816 t s)). Qed.
Lemma lem3845677 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845678 {_99816 : Type'} (s : _99816 -> Prop) : (term45 _99816 s) = (term45 _99816 s).
Proof. exact (MK_COMB (@lem3845677 _99816) (@lem3845676 _99816 s)). Qed.
Lemma lem3845679 {_99816 : Type'} : (term46 _99816) = (term46 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845678 _99816 s)). Qed.
Lemma lem3845680 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845681 {_99816 : Type'} : (term47 _99816) = (term47 _99816).
Proof. exact (MK_COMB (@lem3845680 _99816) (@lem3845679 _99816)). Qed.
Lemma lem3845682 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term48 _99816 s t) = (term48 _99816 s t).
Proof. exact (eq_refl (term48 _99816 s t)). Qed.
Lemma lem3845683 {_99816 : Type'} (s : _99816 -> Prop) : (term49 _99816 s) = (term49 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845682 _99816 s t)). Qed.
Lemma lem3845684 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845685 {_99816 : Type'} (s : _99816 -> Prop) : (term50 _99816 s) = (term50 _99816 s).
Proof. exact (MK_COMB (@lem3845684 _99816) (@lem3845683 _99816 s)). Qed.
Lemma lem3845686 {_99816 : Type'} : (term51 _99816) = (term51 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845685 _99816 s)). Qed.
Lemma lem3845687 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845688 {_99816 : Type'} : (term52 _99816) = (term52 _99816).
Proof. exact (MK_COMB (@lem3845687 _99816) (@lem3845686 _99816)). Qed.
Lemma lem3845689 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3845690 {_99816 : Type'} : (term53 _99816) = (term53 _99816).
Proof. exact (MK_COMB (@lem3845689) (@lem3845688 _99816)). Qed.
Lemma lem3845691 {_99816 : Type'} : (term13 _99816) = (term13 _99816).
Proof. exact (MK_COMB (@lem3845690 _99816) (@lem3845681 _99816)). Qed.
Lemma lem3845692 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3845693 {_99816 : Type'} : (term28 _99816) = (term28 _99816).
Proof. exact (MK_COMB (@lem3845692) (@lem3845691 _99816)). Qed.
Lemma lem3845694 {_99816 A : Type'} : (term32 _99816 A) = (term32 _99816 A).
Proof. exact (MK_COMB (@lem3845693 _99816) (@lem3845674 _99816 A)). Qed.
Lemma lem3845707 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term54 _99816 s t u) = (term54 _99816 s t u).
Proof. exact (eq_refl (term54 _99816 s t u)). Qed.
Lemma lem3845708 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term55 _99816 s t) = (term55 _99816 s t).
Proof. exact (fun_ext (fun u : _99816 -> Prop => @lem3845707 _99816 s t u)). Qed.
Lemma lem3845709 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845710 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term56 _99816 s t) = (term56 _99816 s t).
Proof. exact (MK_COMB (@lem3845709 _99816) (@lem3845708 _99816 s t)). Qed.
Lemma lem3845711 {_99816 : Type'} (s : _99816 -> Prop) : (term57 _99816 s) = (term57 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845710 _99816 s t)). Qed.
Lemma lem3845712 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845713 {_99816 : Type'} (s : _99816 -> Prop) : (term58 _99816 s) = (term58 _99816 s).
Proof. exact (MK_COMB (@lem3845712 _99816) (@lem3845711 _99816 s)). Qed.
Lemma lem3845714 {_99816 : Type'} : (term59 _99816) = (term59 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845713 _99816 s)). Qed.
Lemma lem3845715 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845716 {_99816 : Type'} : (term8 _99816) = (term8 _99816).
Proof. exact (MK_COMB (@lem3845715 _99816) (@lem3845714 _99816)). Qed.
Lemma lem3845717 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3845718 {_99816 : Type'} : (term10 _99816) = (term10 _99816).
Proof. exact (MK_COMB (@lem3845717) (@lem3845716 _99816)). Qed.
Lemma lem3845719 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3845720 {_99816 : Type'} : (term33 _99816) = (term33 _99816).
Proof. exact (MK_COMB (@lem3845719) (@lem3845718 _99816)). Qed.
Lemma lem3845721 {_99816 A : Type'} : (term34 _99816 A) = (term34 _99816 A).
Proof. exact (MK_COMB (@lem3845720 _99816) (@lem3845694 _99816 A)). Qed.
Lemma lem3845880 {_99816 A : Type'} : (term14 _99816 A) = (term34 _99816 A).
Proof. exact (TRANS (@lem3845575 _99816 A) (@lem3845721 _99816 A)). Qed.
Lemma lem3845881 {_99816 A : Type'} : (term34 _99816 A) = (term14 _99816 A).
Proof. exact (SYM (@lem3845880 _99816 A)). Qed.
Lemma lem3845882 {_99816 : Type'} (h1 : term10 _99816) : term10 _99816.
Proof. exact (h1). Qed.
Lemma lem3845883 {_99816 : Type'} (h1 : term13 _99816) : term13 _99816.
Proof. exact (h1). Qed.
Lemma lem3845885 {_99816 : Type'} (h1 : term12 _99816) : term12 _99816.
Proof. exact (h1). Qed.
Lemma lem3845887 {_99816 : Type'} (h1 : term11 _99816) : term11 _99816.
Proof. exact (h1). Qed.
Lemma lem3845903 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term60 _99816 s t u) = (term61 _99816 s t u).
Proof. exact (@lem17362 (term62 _99816 s t u) ((term63 _99816 s t) = (@CARD _99816 u))). Qed.
Lemma lem3845904 {_99816 : Type'} (P : type686 _99816) : (term64 _99816 P) = (term65 _99816 P).
Proof. exact (@lem18392 (_99816 -> Prop) P). Qed.
Lemma lem3845905 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term66 _99816 s t) = (term67 _99816 s t).
Proof. exact (@lem3845904 _99816 (term55 _99816 s t)). Qed.
Lemma lem3845906 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term68 _99816 s t u) = (term54 _99816 s t u).
Proof. exact (eq_refl (term68 _99816 s t u)). Qed.
Lemma lem3845907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3845908 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term69 _99816 s t u) = (term60 _99816 s t u).
Proof. exact (MK_COMB (@lem3845907) (@lem3845906 _99816 s t u)). Qed.
Lemma lem3845909 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term69 _99816 s t u) = (term61 _99816 s t u).
Proof. exact (TRANS (@lem3845908 _99816 s t u) (@lem3845903 _99816 s t u)). Qed.
Lemma lem3845910 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term70 _99816 s t) = (term71 _99816 s t).
Proof. exact (fun_ext (fun u : _99816 -> Prop => @lem3845909 _99816 s t u)). Qed.
Lemma lem3845911 {_99816 : Type'} : (@ex (_99816 -> Prop)) = (@ex (_99816 -> Prop)).
Proof. exact (eq_refl (@ex (_99816 -> Prop))). Qed.
Lemma lem3845912 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term67 _99816 s t) = (term72 _99816 s t).
Proof. exact (MK_COMB (@lem3845911 _99816) (@lem3845910 _99816 s t)). Qed.
Lemma lem3845913 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term66 _99816 s t) = (term72 _99816 s t).
Proof. exact (TRANS (@lem3845905 _99816 s t) (@lem3845912 _99816 s t)). Qed.
Lemma lem3845914 {_99816 : Type'} (P : type686 _99816) : (term64 _99816 P) = (term65 _99816 P).
Proof. exact (@lem18392 (_99816 -> Prop) P). Qed.
Lemma lem3845915 {_99816 : Type'} (s : _99816 -> Prop) : (term73 _99816 s) = (term74 _99816 s).
Proof. exact (@lem3845914 _99816 (term57 _99816 s)). Qed.
Lemma lem3845916 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term75 _99816 s t) = (term56 _99816 s t).
Proof. exact (eq_refl (term75 _99816 s t)). Qed.
Lemma lem3845917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3845918 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term76 _99816 s t) = (term66 _99816 s t).
Proof. exact (MK_COMB (@lem3845917) (@lem3845916 _99816 s t)). Qed.
Lemma lem3845919 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term76 _99816 s t) = (term72 _99816 s t).
Proof. exact (TRANS (@lem3845918 _99816 s t) (@lem3845913 _99816 s t)). Qed.
Lemma lem3845920 {_99816 : Type'} (s : _99816 -> Prop) : (term77 _99816 s) = (term78 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845919 _99816 s t)). Qed.
Lemma lem3845921 {_99816 : Type'} : (@ex (_99816 -> Prop)) = (@ex (_99816 -> Prop)).
Proof. exact (eq_refl (@ex (_99816 -> Prop))). Qed.
Lemma lem3845922 {_99816 : Type'} (s : _99816 -> Prop) : (term74 _99816 s) = (term79 _99816 s).
Proof. exact (MK_COMB (@lem3845921 _99816) (@lem3845920 _99816 s)). Qed.
Lemma lem3845923 {_99816 : Type'} (s : _99816 -> Prop) : (term73 _99816 s) = (term79 _99816 s).
Proof. exact (TRANS (@lem3845915 _99816 s) (@lem3845922 _99816 s)). Qed.
Lemma lem3845924 {_99816 : Type'} (P : type686 _99816) : (term64 _99816 P) = (term65 _99816 P).
Proof. exact (@lem18392 (_99816 -> Prop) P). Qed.
Lemma lem3845925 {_99816 : Type'} : (term10 _99816) = (term80 _99816).
Proof. exact (@lem3845924 _99816 (term59 _99816)). Qed.
Lemma lem3845926 {_99816 : Type'} (s : _99816 -> Prop) : (term81 _99816 s) = (term58 _99816 s).
Proof. exact (eq_refl (term81 _99816 s)). Qed.
Lemma lem3845927 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3845928 {_99816 : Type'} (s : _99816 -> Prop) : (term82 _99816 s) = (term73 _99816 s).
Proof. exact (MK_COMB (@lem3845927) (@lem3845926 _99816 s)). Qed.
Lemma lem3845929 {_99816 : Type'} (s : _99816 -> Prop) : (term82 _99816 s) = (term79 _99816 s).
Proof. exact (TRANS (@lem3845928 _99816 s) (@lem3845923 _99816 s)). Qed.
Lemma lem3845930 {_99816 : Type'} : (term83 _99816) = (term84 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845929 _99816 s)). Qed.
Lemma lem3845931 {_99816 : Type'} : (@ex (_99816 -> Prop)) = (@ex (_99816 -> Prop)).
Proof. exact (eq_refl (@ex (_99816 -> Prop))). Qed.
Lemma lem3845932 {_99816 : Type'} : (term80 _99816) = (term85 _99816).
Proof. exact (MK_COMB (@lem3845931 _99816) (@lem3845930 _99816)). Qed.
Lemma lem3845993 {_99816 : Type'} : (term10 _99816) = (term85 _99816).
Proof. exact (TRANS (@lem3845925 _99816) (@lem3845932 _99816)). Qed.
Lemma lem3845994 {_99816 : Type'} (h1 : term10 _99816) : term85 _99816.
Proof. exact (EQ_MP (@lem3845993 _99816) (@lem3845882 _99816 h1)). Qed.
Lemma lem3845995 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term48 _99816 s t) = (term48 _99816 s t).
Proof. exact (eq_refl (term48 _99816 s t)). Qed.
Lemma lem3845996 {_99816 : Type'} (s : _99816 -> Prop) : (term49 _99816 s) = (term49 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3845995 _99816 s t)). Qed.
Lemma lem3845997 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3845998 {_99816 : Type'} (s : _99816 -> Prop) : (term50 _99816 s) = (term50 _99816 s).
Proof. exact (MK_COMB (@lem3845997 _99816) (@lem3845996 _99816 s)). Qed.
Lemma lem3845999 {_99816 : Type'} : (term51 _99816) = (term51 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3845998 _99816 s)). Qed.
Lemma lem3846000 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846001 {_99816 : Type'} : (term52 _99816) = (term52 _99816).
Proof. exact (MK_COMB (@lem3846000 _99816) (@lem3845999 _99816)). Qed.
Lemma lem3846002 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term43 _99816 t s) = (term43 _99816 t s).
Proof. exact (eq_refl (term43 _99816 t s)). Qed.
Lemma lem3846003 {_99816 : Type'} (s : _99816 -> Prop) : (term44 _99816 s) = (term44 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846002 _99816 t s)). Qed.
Lemma lem3846004 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846005 {_99816 : Type'} (s : _99816 -> Prop) : (term45 _99816 s) = (term45 _99816 s).
Proof. exact (MK_COMB (@lem3846004 _99816) (@lem3846003 _99816 s)). Qed.
Lemma lem3846006 {_99816 : Type'} : (term46 _99816) = (term46 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846005 _99816 s)). Qed.
Lemma lem3846007 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846008 {_99816 : Type'} : (term47 _99816) = (term47 _99816).
Proof. exact (MK_COMB (@lem3846007 _99816) (@lem3846006 _99816)). Qed.
Lemma lem3846009 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3846010 {_99816 : Type'} : (term53 _99816) = (term53 _99816).
Proof. exact (MK_COMB (@lem3846009) (@lem3846001 _99816)). Qed.
Lemma lem3846031 {_99816 : Type'} : (term13 _99816) = (term13 _99816).
Proof. exact (MK_COMB (@lem3846010 _99816) (@lem3846008 _99816)). Qed.
Lemma lem3846032 {_99816 : Type'} (h1 : term13 _99816) : term13 _99816.
Proof. exact (EQ_MP (@lem3846031 _99816) (@lem3845883 _99816 h1)). Qed.
Lemma lem3846077 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term86 _99816 s t) = (term87 _99816 s t).
Proof. exact (@lem17045 (@FINITE _99816 t) (@SUBSET _99816 s t)). Qed.
Lemma lem3846078 {_99816 : Type'} (s : _99816 -> Prop) : (@FINITE _99816 s) = (@FINITE _99816 s).
Proof. exact (eq_refl (@FINITE _99816 s)). Qed.
Lemma lem3846079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846080 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term88 _99816 s t) = (term89 _99816 s t).
Proof. exact (MK_COMB (@lem3846079) (@lem3846077 _99816 s t)). Qed.
Lemma lem3846081 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term90 _99816 t s) = (term91 _99816 t s).
Proof. exact (MK_COMB (@lem3846080 _99816 s t) (@lem3846078 _99816 s)). Qed.
Lemma lem3846082 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term39 _99816 t s) = (term90 _99816 t s).
Proof. exact (@lem17265 (term92 _99816 s t) (@FINITE _99816 s)). Qed.
Lemma lem3846083 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term39 _99816 t s) = (term91 _99816 t s).
Proof. exact (TRANS (@lem3846082 _99816 t s) (@lem3846081 _99816 t s)). Qed.
Lemma lem3846084 {_99816 : Type'} (s : _99816 -> Prop) : (term40 _99816 s) = (term93 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846083 _99816 t s)). Qed.
Lemma lem3846085 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846086 {_99816 : Type'} (s : _99816 -> Prop) : (term41 _99816 s) = (term94 _99816 s).
Proof. exact (MK_COMB (@lem3846085 _99816) (@lem3846084 _99816 s)). Qed.
Lemma lem3846087 {_99816 : Type'} : (term42 _99816) = (term95 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846086 _99816 s)). Qed.
Lemma lem3846088 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846089 {_99816 : Type'} : (term12 _99816) = (term96 _99816).
Proof. exact (MK_COMB (@lem3846088 _99816) (@lem3846087 _99816)). Qed.
Lemma lem3846115 {A : Type'} (P : A -> Prop) (Q : Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem3846116 {_99816 : Type'} (P : type686 _99816) (Q : Prop) : (term99 _99816 P Q) = (term100 _99816 P Q).
Proof. exact (@lem3846115 (_99816 -> Prop) P Q). Qed.
Lemma lem3846117 {_99816 : Type'} (s : _99816 -> Prop) : (term101 _99816 s) = (term102 _99816 s).
Proof. exact (@lem3846116 _99816 (term103 _99816 s) (@FINITE _99816 s)). Qed.
Lemma lem3846118 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term104 _99816 s t) = (term87 _99816 s t).
Proof. exact (eq_refl (term104 _99816 s t)). Qed.
Lemma lem3846119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846120 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term105 _99816 s t) = (term89 _99816 s t).
Proof. exact (MK_COMB (@lem3846119) (@lem3846118 _99816 s t)). Qed.
Lemma lem3846121 {_99816 : Type'} (s : _99816 -> Prop) : (@FINITE _99816 s) = (@FINITE _99816 s).
Proof. exact (eq_refl (@FINITE _99816 s)). Qed.
Lemma lem3846122 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term106 _99816 t s) = (term91 _99816 t s).
Proof. exact (MK_COMB (@lem3846120 _99816 s t) (@lem3846121 _99816 s)). Qed.
Lemma lem3846123 {_99816 : Type'} (s : _99816 -> Prop) : (term107 _99816 s) = (term93 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846122 _99816 t s)). Qed.
Lemma lem3846124 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846125 {_99816 : Type'} (s : _99816 -> Prop) : (term101 _99816 s) = (term94 _99816 s).
Proof. exact (MK_COMB (@lem3846124 _99816) (@lem3846123 _99816 s)). Qed.
Lemma lem3846126 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3846127 {_99816 : Type'} (s : _99816 -> Prop) : (term108 _99816 s) = (term109 _99816 s).
Proof. exact (MK_COMB (@lem3846126) (@lem3846125 _99816 s)). Qed.
Lemma lem3846128 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term104 _99816 s t) = (term87 _99816 s t).
Proof. exact (eq_refl (term104 _99816 s t)). Qed.
Lemma lem3846129 {_99816 : Type'} (s : _99816 -> Prop) : (term110 _99816 s) = (term103 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846128 _99816 s t)). Qed.
Lemma lem3846130 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846131 {_99816 : Type'} (s : _99816 -> Prop) : (term111 _99816 s) = (term112 _99816 s).
Proof. exact (MK_COMB (@lem3846130 _99816) (@lem3846129 _99816 s)). Qed.
Lemma lem3846132 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846133 {_99816 : Type'} (s : _99816 -> Prop) : (term113 _99816 s) = (term114 _99816 s).
Proof. exact (MK_COMB (@lem3846132) (@lem3846131 _99816 s)). Qed.
Lemma lem3846134 {_99816 : Type'} (s : _99816 -> Prop) : (@FINITE _99816 s) = (@FINITE _99816 s).
Proof. exact (eq_refl (@FINITE _99816 s)). Qed.
Lemma lem3846135 {_99816 : Type'} (s : _99816 -> Prop) : (term102 _99816 s) = (term115 _99816 s).
Proof. exact (MK_COMB (@lem3846133 _99816 s) (@lem3846134 _99816 s)). Qed.
Lemma lem3846136 {_99816 : Type'} (s : _99816 -> Prop) : ((term101 _99816 s) = (term102 _99816 s)) = ((term94 _99816 s) = (term115 _99816 s)).
Proof. exact (MK_COMB (@lem3846127 _99816 s) (@lem3846135 _99816 s)). Qed.
Lemma lem3846137 {_99816 : Type'} (s : _99816 -> Prop) : (term94 _99816 s) = (term115 _99816 s).
Proof. exact (EQ_MP (@lem3846136 _99816 s) (@lem3846117 _99816 s)). Qed.
Lemma lem3846186 {_99816 : Type'} : (term95 _99816) = (term116 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846137 _99816 s)). Qed.
Lemma lem3846187 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846222 {_99816 : Type'} : (term96 _99816) = (term117 _99816).
Proof. exact (MK_COMB (@lem3846187 _99816) (@lem3846186 _99816)). Qed.
Lemma lem3846223 {_99816 : Type'} : (term12 _99816) = (term117 _99816).
Proof. exact (TRANS (@lem3846089 _99816) (@lem3846222 _99816)). Qed.
Lemma lem3846224 {_99816 : Type'} (h1 : term12 _99816) : term117 _99816.
Proof. exact (EQ_MP (@lem3846223 _99816) (@lem3845885 _99816 h1)). Qed.
Lemma lem3846386 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term118 _99816 s t) = (term119 _99816 s t).
Proof. exact (@lem17045 (@FINITE _99816 t) ((@INTER _99816 s t) = (@EMPTY _99816))). Qed.
Lemma lem3846388 {_99816 : Type'} (s : _99816 -> Prop) : (term120 _99816 s) = (term120 _99816 s).
Proof. exact (eq_refl (term120 _99816 s)). Qed.
Lemma lem3846389 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term121 _99816 s t) = (term122 _99816 s t).
Proof. exact (MK_COMB (@lem3846388 _99816 s) (@lem3846386 _99816 s t)). Qed.
Lemma lem3846390 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term123 _99816 s t) = (term121 _99816 s t).
Proof. exact (@lem17045 (@FINITE _99816 s) (term124 _99816 s t)). Qed.
Lemma lem3846391 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term123 _99816 s t) = (term122 _99816 s t).
Proof. exact (TRANS (@lem3846390 _99816 s t) (@lem3846389 _99816 s t)). Qed.
Lemma lem3846392 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term125 _99816 s t) = (term63 _99816 s t)) = ((term125 _99816 s t) = (term63 _99816 s t)).
Proof. exact (eq_refl ((term125 _99816 s t) = (term63 _99816 s t))). Qed.
Lemma lem3846393 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846394 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term126 _99816 s t) = (term127 _99816 s t).
Proof. exact (MK_COMB (@lem3846393) (@lem3846391 _99816 s t)). Qed.
Lemma lem3846395 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term128 _99816 s t) = (term129 _99816 s t).
Proof. exact (MK_COMB (@lem3846394 _99816 s t) (@lem3846392 _99816 s t)). Qed.
Lemma lem3846396 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term35 _99816 s t) = (term128 _99816 s t).
Proof. exact (@lem17265 (term130 _99816 s t) ((term125 _99816 s t) = (term63 _99816 s t))). Qed.
Lemma lem3846397 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term35 _99816 s t) = (term129 _99816 s t).
Proof. exact (TRANS (@lem3846396 _99816 s t) (@lem3846395 _99816 s t)). Qed.
Lemma lem3846398 {_99816 : Type'} (s : _99816 -> Prop) : (term36 _99816 s) = (term131 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846397 _99816 s t)). Qed.
Lemma lem3846399 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846400 {_99816 : Type'} (s : _99816 -> Prop) : (term37 _99816 s) = (term132 _99816 s).
Proof. exact (MK_COMB (@lem3846399 _99816) (@lem3846398 _99816 s)). Qed.
Lemma lem3846401 {_99816 : Type'} : (term38 _99816) = (term133 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846400 _99816 s)). Qed.
Lemma lem3846402 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846459 {_99816 : Type'} : (term11 _99816) = (term134 _99816).
Proof. exact (MK_COMB (@lem3846402 _99816) (@lem3846401 _99816)). Qed.
Lemma lem3846460 {_99816 : Type'} (h1 : term11 _99816) : term134 _99816.
Proof. exact (EQ_MP (@lem3846459 _99816) (@lem3845887 _99816 h1)). Qed.
Lemma lem3846543 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term79 _99816 s) : term79 _99816 s.
Proof. exact (h1). Qed.
Lemma lem3846544 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term72 _99816 s t) : term72 _99816 s t.
Proof. exact (h1). Qed.
Lemma lem3846554 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term43 _99816 t s) = (term43 _99816 t s).
Proof. exact (eq_refl (term43 _99816 t s)). Qed.
Lemma lem3846555 {_99816 : Type'} (s : _99816 -> Prop) : (term44 _99816 s) = (term44 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846554 _99816 t s)). Qed.
Lemma lem3846556 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846557 {_99816 : Type'} (s : _99816 -> Prop) : (term45 _99816 s) = (term45 _99816 s).
Proof. exact (MK_COMB (@lem3846556 _99816) (@lem3846555 _99816 s)). Qed.
Lemma lem3846558 {_99816 : Type'} : (term46 _99816) = (term46 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846557 _99816 s)). Qed.
Lemma lem3846559 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846560 {_99816 : Type'} : (term47 _99816) = (term47 _99816).
Proof. exact (MK_COMB (@lem3846559 _99816) (@lem3846558 _99816)). Qed.
Lemma lem3846569 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term48 _99816 s t) = (term48 _99816 s t).
Proof. exact (eq_refl (term48 _99816 s t)). Qed.
Lemma lem3846570 {_99816 : Type'} (s : _99816 -> Prop) : (term49 _99816 s) = (term49 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846569 _99816 s t)). Qed.
Lemma lem3846571 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846572 {_99816 : Type'} (s : _99816 -> Prop) : (term50 _99816 s) = (term50 _99816 s).
Proof. exact (MK_COMB (@lem3846571 _99816) (@lem3846570 _99816 s)). Qed.
Lemma lem3846573 {_99816 : Type'} : (term51 _99816) = (term51 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846572 _99816 s)). Qed.
Lemma lem3846574 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846575 {_99816 : Type'} : (term52 _99816) = (term52 _99816).
Proof. exact (MK_COMB (@lem3846574 _99816) (@lem3846573 _99816)). Qed.
Lemma lem3846576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3846577 {_99816 : Type'} : (term53 _99816) = (term53 _99816).
Proof. exact (MK_COMB (@lem3846576) (@lem3846575 _99816)). Qed.
Lemma lem3846578 {_99816 : Type'} : (term13 _99816) = (term13 _99816).
Proof. exact (MK_COMB (@lem3846577 _99816) (@lem3846560 _99816)). Qed.
Lemma lem3846579 {_99816 : Type'} (h1 : term13 _99816) : term13 _99816.
Proof. exact (EQ_MP (@lem3846578 _99816) (@lem3846032 _99816 h1)). Qed.
Lemma lem3846616 {_99816 : Type'} (s : _99816 -> Prop) : (@FINITE _99816 s) = (@FINITE _99816 s).
Proof. exact (eq_refl (@FINITE _99816 s)). Qed.
Lemma lem3846631 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term87 _99816 s t) = (term87 _99816 s t).
Proof. exact (eq_refl (term87 _99816 s t)). Qed.
Lemma lem3846632 {_99816 : Type'} (s : _99816 -> Prop) : (term103 _99816 s) = (term103 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846631 _99816 s t)). Qed.
Lemma lem3846633 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846634 {_99816 : Type'} (s : _99816 -> Prop) : (term112 _99816 s) = (term112 _99816 s).
Proof. exact (MK_COMB (@lem3846633 _99816) (@lem3846632 _99816 s)). Qed.
Lemma lem3846635 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846636 {_99816 : Type'} (s : _99816 -> Prop) : (term114 _99816 s) = (term114 _99816 s).
Proof. exact (MK_COMB (@lem3846635) (@lem3846634 _99816 s)). Qed.
Lemma lem3846637 {_99816 : Type'} (s : _99816 -> Prop) : (term115 _99816 s) = (term115 _99816 s).
Proof. exact (MK_COMB (@lem3846636 _99816 s) (@lem3846616 _99816 s)). Qed.
Lemma lem3846638 {_99816 : Type'} : (term116 _99816) = (term116 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846637 _99816 s)). Qed.
Lemma lem3846639 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846640 {_99816 : Type'} : (term117 _99816) = (term117 _99816).
Proof. exact (MK_COMB (@lem3846639 _99816) (@lem3846638 _99816)). Qed.
Lemma lem3846641 {_99816 : Type'} (h1 : term12 _99816) : term117 _99816.
Proof. exact (EQ_MP (@lem3846640 _99816) (@lem3846224 _99816 h1)). Qed.
Lemma lem3846718 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term129 _99816 s t) = (term129 _99816 s t).
Proof. exact (eq_refl (term129 _99816 s t)). Qed.
Lemma lem3846719 {_99816 : Type'} (s : _99816 -> Prop) : (term131 _99816 s) = (term131 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846718 _99816 s t)). Qed.
Lemma lem3846720 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846721 {_99816 : Type'} (s : _99816 -> Prop) : (term132 _99816 s) = (term132 _99816 s).
Proof. exact (MK_COMB (@lem3846720 _99816) (@lem3846719 _99816 s)). Qed.
Lemma lem3846722 {_99816 : Type'} : (term133 _99816) = (term133 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846721 _99816 s)). Qed.
Lemma lem3846723 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846724 {_99816 : Type'} : (term134 _99816) = (term134 _99816).
Proof. exact (MK_COMB (@lem3846723 _99816) (@lem3846722 _99816)). Qed.
Lemma lem3846725 {_99816 : Type'} (h1 : term11 _99816) : term134 _99816.
Proof. exact (EQ_MP (@lem3846724 _99816) (@lem3846460 _99816 h1)). Qed.
Lemma lem3846829 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term61 _99816 s t u.
Proof. exact (h1). Qed.
Lemma lem3846831 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term62 _99816 s t u.
Proof. exact (proj1 (@lem3846829 _99816 s t u h1)). Qed.
Lemma lem3846832 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term135 _99816 s t u.
Proof. exact (proj2 (@lem3846831 _99816 s t u h1)). Qed.
Lemma lem3846838 {_99816 : Type'} (h1 : term13 _99816) : term47 _99816.
Proof. exact (proj2 (@lem3846579 _99816 h1)). Qed.
Lemma lem3846839 {_99816 : Type'} (h1 : term13 _99816) : term52 _99816.
Proof. exact (proj1 (@lem3846579 _99816 h1)). Qed.
Lemma lem3846841 {A : Type'} (P : A -> Prop) (Q : Prop) : (term98 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3846842 {_99816 : Type'} (P : type686 _99816) (Q : Prop) : (term100 _99816 P Q) = (term99 _99816 P Q).
Proof. exact (@lem3846841 (_99816 -> Prop) P Q). Qed.
Lemma lem3846843 {_99816 : Type'} (s : _99816 -> Prop) : (term102 _99816 s) = (term101 _99816 s).
Proof. exact (@lem3846842 _99816 (term103 _99816 s) (@FINITE _99816 s)). Qed.
Lemma lem3846844 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term104 _99816 s t) = (term87 _99816 s t).
Proof. exact (eq_refl (term104 _99816 s t)). Qed.
Lemma lem3846845 {_99816 : Type'} (s : _99816 -> Prop) : (term110 _99816 s) = (term103 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846844 _99816 s t)). Qed.
Lemma lem3846846 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846847 {_99816 : Type'} (s : _99816 -> Prop) : (term111 _99816 s) = (term112 _99816 s).
Proof. exact (MK_COMB (@lem3846846 _99816) (@lem3846845 _99816 s)). Qed.
Lemma lem3846848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846849 {_99816 : Type'} (s : _99816 -> Prop) : (term113 _99816 s) = (term114 _99816 s).
Proof. exact (MK_COMB (@lem3846848) (@lem3846847 _99816 s)). Qed.
Lemma lem3846850 {_99816 : Type'} (s : _99816 -> Prop) : (@FINITE _99816 s) = (@FINITE _99816 s).
Proof. exact (eq_refl (@FINITE _99816 s)). Qed.
Lemma lem3846851 {_99816 : Type'} (s : _99816 -> Prop) : (term102 _99816 s) = (term115 _99816 s).
Proof. exact (MK_COMB (@lem3846849 _99816 s) (@lem3846850 _99816 s)). Qed.
Lemma lem3846852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3846853 {_99816 : Type'} (s : _99816 -> Prop) : (term136 _99816 s) = (term137 _99816 s).
Proof. exact (MK_COMB (@lem3846852) (@lem3846851 _99816 s)). Qed.
Lemma lem3846854 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term104 _99816 s t) = (term87 _99816 s t).
Proof. exact (eq_refl (term104 _99816 s t)). Qed.
Lemma lem3846855 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3846856 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term105 _99816 s t) = (term89 _99816 s t).
Proof. exact (MK_COMB (@lem3846855) (@lem3846854 _99816 s t)). Qed.
Lemma lem3846857 {_99816 : Type'} (s : _99816 -> Prop) : (@FINITE _99816 s) = (@FINITE _99816 s).
Proof. exact (eq_refl (@FINITE _99816 s)). Qed.
Lemma lem3846858 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term106 _99816 t s) = (term91 _99816 t s).
Proof. exact (MK_COMB (@lem3846856 _99816 s t) (@lem3846857 _99816 s)). Qed.
Lemma lem3846859 {_99816 : Type'} (s : _99816 -> Prop) : (term107 _99816 s) = (term93 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846858 _99816 t s)). Qed.
Lemma lem3846860 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846861 {_99816 : Type'} (s : _99816 -> Prop) : (term101 _99816 s) = (term94 _99816 s).
Proof. exact (MK_COMB (@lem3846860 _99816) (@lem3846859 _99816 s)). Qed.
Lemma lem3846862 {_99816 : Type'} (s : _99816 -> Prop) : ((term102 _99816 s) = (term101 _99816 s)) = ((term115 _99816 s) = (term94 _99816 s)).
Proof. exact (MK_COMB (@lem3846853 _99816 s) (@lem3846861 _99816 s)). Qed.
Lemma lem3846863 {_99816 : Type'} (s : _99816 -> Prop) : (term115 _99816 s) = (term94 _99816 s).
Proof. exact (EQ_MP (@lem3846862 _99816 s) (@lem3846843 _99816 s)). Qed.
Lemma lem3846864 {_99816 : Type'} : (term116 _99816) = (term95 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846863 _99816 s)). Qed.
Lemma lem3846865 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846866 {_99816 : Type'} : (term117 _99816) = (term96 _99816).
Proof. exact (MK_COMB (@lem3846865 _99816) (@lem3846864 _99816)). Qed.
Lemma lem3846879 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term91 _99816 t s) = (term91 _99816 t s).
Proof. exact (eq_refl (term91 _99816 t s)). Qed.
Lemma lem3846880 {_99816 : Type'} (s : _99816 -> Prop) : (term93 _99816 s) = (term93 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846879 _99816 t s)). Qed.
Lemma lem3846881 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846882 {_99816 : Type'} (s : _99816 -> Prop) : (term94 _99816 s) = (term94 _99816 s).
Proof. exact (MK_COMB (@lem3846881 _99816) (@lem3846880 _99816 s)). Qed.
Lemma lem3846883 {_99816 : Type'} : (term95 _99816) = (term95 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846882 _99816 s)). Qed.
Lemma lem3846884 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846885 {_99816 : Type'} : (term96 _99816) = (term96 _99816).
Proof. exact (MK_COMB (@lem3846884 _99816) (@lem3846883 _99816)). Qed.
Lemma lem3846886 {_99816 : Type'} : (term117 _99816) = (term96 _99816).
Proof. exact (TRANS (@lem3846866 _99816) (@lem3846885 _99816)). Qed.
Lemma lem3846887 {_99816 : Type'} (h1 : term12 _99816) : term96 _99816.
Proof. exact (EQ_MP (@lem3846886 _99816) (@lem3846641 _99816 h1)). Qed.
Lemma lem3846955 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term129 _99816 s t) = (term129 _99816 s t).
Proof. exact (eq_refl (term129 _99816 s t)). Qed.
Lemma lem3846956 {_99816 : Type'} (s : _99816 -> Prop) : (term131 _99816 s) = (term131 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3846955 _99816 s t)). Qed.
Lemma lem3846957 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846958 {_99816 : Type'} (s : _99816 -> Prop) : (term132 _99816 s) = (term132 _99816 s).
Proof. exact (MK_COMB (@lem3846957 _99816) (@lem3846956 _99816 s)). Qed.
Lemma lem3846959 {_99816 : Type'} : (term133 _99816) = (term133 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3846958 _99816 s)). Qed.
Lemma lem3846960 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3846962 {_99816 : Type'} : (term134 _99816) = (term134 _99816).
Proof. exact (MK_COMB (@lem3846960 _99816) (@lem3846959 _99816)). Qed.
Lemma lem3846963 {_99816 : Type'} (h1 : term11 _99816) : term134 _99816.
Proof. exact (EQ_MP (@lem3846962 _99816) (@lem3846725 _99816 h1)). Qed.
Lemma lem3847029 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term48 _99816 s t) = (term48 _99816 s t).
Proof. exact (eq_refl (term48 _99816 s t)). Qed.
Lemma lem3847030 {_99816 : Type'} (s : _99816 -> Prop) : (term49 _99816 s) = (term49 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3847029 _99816 s t)). Qed.
Lemma lem3847031 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3847032 {_99816 : Type'} (s : _99816 -> Prop) : (term50 _99816 s) = (term50 _99816 s).
Proof. exact (MK_COMB (@lem3847031 _99816) (@lem3847030 _99816 s)). Qed.
Lemma lem3847033 {_99816 : Type'} : (term51 _99816) = (term51 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3847032 _99816 s)). Qed.
Lemma lem3847034 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3847036 {_99816 : Type'} : (term52 _99816) = (term52 _99816).
Proof. exact (MK_COMB (@lem3847034 _99816) (@lem3847033 _99816)). Qed.
Lemma lem3847037 {_99816 : Type'} (h1 : term13 _99816) : term52 _99816.
Proof. exact (EQ_MP (@lem3847036 _99816) (@lem3846839 _99816 h1)). Qed.
Lemma lem3847039 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) : (term43 _99816 t s) = (term43 _99816 t s).
Proof. exact (eq_refl (term43 _99816 t s)). Qed.
Lemma lem3847040 {_99816 : Type'} (s : _99816 -> Prop) : (term44 _99816 s) = (term44 _99816 s).
Proof. exact (fun_ext (fun t : _99816 -> Prop => @lem3847039 _99816 t s)). Qed.
Lemma lem3847041 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3847042 {_99816 : Type'} (s : _99816 -> Prop) : (term45 _99816 s) = (term45 _99816 s).
Proof. exact (MK_COMB (@lem3847041 _99816) (@lem3847040 _99816 s)). Qed.
Lemma lem3847043 {_99816 : Type'} : (term46 _99816) = (term46 _99816).
Proof. exact (fun_ext (fun s : _99816 -> Prop => @lem3847042 _99816 s)). Qed.
Lemma lem3847044 {_99816 : Type'} : (@all (_99816 -> Prop)) = (@all (_99816 -> Prop)).
Proof. exact (eq_refl (@all (_99816 -> Prop))). Qed.
Lemma lem3847046 {_99816 : Type'} : (term47 _99816) = (term47 _99816).
Proof. exact (MK_COMB (@lem3847044 _99816) (@lem3847043 _99816)). Qed.
Lemma lem3847047 {_99816 : Type'} (h1 : term13 _99816) : term47 _99816.
Proof. exact (EQ_MP (@lem3847046 _99816) (@lem3846838 _99816 h1)). Qed.
Lemma lem3847048 {_99816 : Type'} (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term138 _99816 _44634.
Proof. exact (@lem3846887 _99816 h1 _44634). Qed.
Lemma lem3847049 {_99816 : Type'} (_44634 : _99816 -> Prop) : (term138 _99816 _44634) = (term94 _99816 _44634).
Proof. exact (eq_refl (term138 _99816 _44634)). Qed.
Lemma lem3847050 {_99816 : Type'} (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term94 _99816 _44634.
Proof. exact (EQ_MP (@lem3847049 _99816 _44634) (@lem3847048 _99816 _44634 h1)). Qed.
Lemma lem3847051 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) (h1 : term12 _99816) : term139 _99816 _44634 _44635.
Proof. exact (@lem3847050 _99816 _44634 h1 _44635). Qed.
Lemma lem3847052 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) : (term139 _99816 _44634 _44635) = (term91 _99816 _44635 _44634).
Proof. exact (eq_refl (term139 _99816 _44634 _44635)). Qed.
Lemma lem3847053 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term91 _99816 _44635 _44634.
Proof. exact (EQ_MP (@lem3847052 _99816 _44635 _44634) (@lem3847051 _99816 _44634 _44635 h1)). Qed.
Lemma lem3847060 {_99816 : Type'} (_44638 : _99816 -> Prop) (h1 : term11 _99816) : term140 _99816 _44638.
Proof. exact (@lem3846963 _99816 h1 _44638). Qed.
Lemma lem3847061 {_99816 : Type'} (_44638 : _99816 -> Prop) : (term140 _99816 _44638) = (term132 _99816 _44638).
Proof. exact (eq_refl (term140 _99816 _44638)). Qed.
Lemma lem3847062 {_99816 : Type'} (_44638 : _99816 -> Prop) (h1 : term11 _99816) : term132 _99816 _44638.
Proof. exact (EQ_MP (@lem3847061 _99816 _44638) (@lem3847060 _99816 _44638 h1)). Qed.
Lemma lem3847063 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (h1 : term11 _99816) : term141 _99816 _44638 _44639.
Proof. exact (@lem3847062 _99816 _44638 h1 _44639). Qed.
Lemma lem3847064 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term141 _99816 _44638 _44639) = (term129 _99816 _44638 _44639).
Proof. exact (eq_refl (term141 _99816 _44638 _44639)). Qed.
Lemma lem3847065 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (h1 : term11 _99816) : term129 _99816 _44638 _44639.
Proof. exact (EQ_MP (@lem3847064 _99816 _44638 _44639) (@lem3847063 _99816 _44638 _44639 h1)). Qed.
Lemma lem3847084 {_99816 : Type'} (_44646 : _99816 -> Prop) (h1 : term13 _99816) : term142 _99816 _44646.
Proof. exact (@lem3847037 _99816 h1 _44646). Qed.
Lemma lem3847085 {_99816 : Type'} (_44646 : _99816 -> Prop) : (term142 _99816 _44646) = (term50 _99816 _44646).
Proof. exact (eq_refl (term142 _99816 _44646)). Qed.
Lemma lem3847086 {_99816 : Type'} (_44646 : _99816 -> Prop) (h1 : term13 _99816) : term50 _99816 _44646.
Proof. exact (EQ_MP (@lem3847085 _99816 _44646) (@lem3847084 _99816 _44646 h1)). Qed.
Lemma lem3847087 {_99816 : Type'} (_44646 : _99816 -> Prop) (_44647 : _99816 -> Prop) (h1 : term13 _99816) : term143 _99816 _44646 _44647.
Proof. exact (@lem3847086 _99816 _44646 h1 _44647). Qed.
Lemma lem3847088 {_99816 : Type'} (_44646 : _99816 -> Prop) (_44647 : _99816 -> Prop) : (term143 _99816 _44646 _44647) = (term48 _99816 _44646 _44647).
Proof. exact (eq_refl (term143 _99816 _44646 _44647)). Qed.
Lemma lem3847090 {_99816 : Type'} (_44648 : _99816 -> Prop) (h1 : term13 _99816) : term144 _99816 _44648.
Proof. exact (@lem3847047 _99816 h1 _44648). Qed.
Lemma lem3847091 {_99816 : Type'} (_44648 : _99816 -> Prop) : (term144 _99816 _44648) = (term45 _99816 _44648).
Proof. exact (eq_refl (term144 _99816 _44648)). Qed.
Lemma lem3847092 {_99816 : Type'} (_44648 : _99816 -> Prop) (h1 : term13 _99816) : term45 _99816 _44648.
Proof. exact (EQ_MP (@lem3847091 _99816 _44648) (@lem3847090 _99816 _44648 h1)). Qed.
Lemma lem3847093 {_99816 : Type'} (_44648 : _99816 -> Prop) (_44649 : _99816 -> Prop) (h1 : term13 _99816) : term145 _99816 _44648 _44649.
Proof. exact (@lem3847092 _99816 _44648 h1 _44649). Qed.
Lemma lem3847094 {_99816 : Type'} (_44649 : _99816 -> Prop) (_44648 : _99816 -> Prop) : (term145 _99816 _44648 _44649) = (term43 _99816 _44649 _44648).
Proof. exact (eq_refl (term145 _99816 _44648 _44649)). Qed.
Lemma lem3847106 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) : (term91 _99816 _44635 _44634) = (term146 _99816 _44635 _44634).
Proof. exact (@lem3845393 (term147 _99816 _44635) (term148 _99816 _44634 _44635) (@FINITE _99816 _44634)). Qed.
Lemma lem3847123 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term129 _99816 _44638 _44639) = (term149 _99816 _44638 _44639).
Proof. exact (@lem3845393 (term147 _99816 _44638) (term119 _99816 _44638 _44639) ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639))). Qed.
Lemma lem3847130 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term150 _99816 _44638 _44639) = (term151 _99816 _44638 _44639).
Proof. exact (@lem3845393 (term147 _99816 _44639) (term152 _99816 _44638 _44639) ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639))). Qed.
Lemma lem3847131 {_99816 : Type'} (_44638 : _99816 -> Prop) : (term120 _99816 _44638) = (term120 _99816 _44638).
Proof. exact (eq_refl (term120 _99816 _44638)). Qed.
Lemma lem3847134 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term149 _99816 _44638 _44639) = (term153 _99816 _44638 _44639).
Proof. exact (MK_COMB (@lem3847131 _99816 _44638) (@lem3847130 _99816 _44638 _44639)). Qed.
Lemma lem3847136 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term129 _99816 _44638 _44639) = (term153 _99816 _44638 _44639).
Proof. exact (TRANS (@lem3847123 _99816 _44638 _44639) (@lem3847134 _99816 _44638 _44639)). Qed.
Lemma lem3847157 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term154 _99816 s t u.
Proof. exact (proj2 (@lem3846829 _99816 s t u h1)). Qed.
Lemma lem3847159 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : @FINITE _99816 u.
Proof. exact (proj1 (@lem3846831 _99816 s t u h1)). Qed.
Lemma lem3847163 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (@UNION _99816 s t) = u.
Proof. exact (proj2 (@lem3846832 _99816 s t u h1)). Qed.
Lemma lem3847172 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : u = (@UNION _99816 s t).
Proof. exact (SYM (@lem3847163 _99816 s t u h1)). Qed.
Lemma lem3847228 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (h1 : term11 _99816) : term153 _99816 _44638 _44639.
Proof. exact (EQ_MP (@lem3847136 _99816 _44638 _44639) (@lem3847065 _99816 _44638 _44639 h1)). Qed.
Lemma lem3847243 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term155 _99816 s t) = (term155 _99816 s t).
Proof. exact (eq_refl (term155 _99816 s t)). Qed.
Lemma lem3847244 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (term156 _99816 s t u) = (term157 _99816 s t).
Proof. exact (MK_COMB (@lem3847243 _99816 s t) (@lem3847172 _99816 s t u h1)). Qed.
Lemma lem3847245 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term157 _99816 s t) = (term158 _99816 s t).
Proof. exact (eq_refl (term157 _99816 s t)). Qed.
Lemma lem3847246 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term159 _99816 s t u) = (term159 _99816 s t u).
Proof. exact (eq_refl (term159 _99816 s t u)). Qed.
Lemma lem3847247 {_99816 : Type'} (u : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term156 _99816 s t u) = (term157 _99816 s t)) = ((term156 _99816 s t u) = (term158 _99816 s t)).
Proof. exact (MK_COMB (@lem3847246 _99816 s t u) (@lem3847245 _99816 s t)). Qed.
Lemma lem3847248 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term156 _99816 s t u) = (term154 _99816 s t u).
Proof. exact (eq_refl (term156 _99816 s t u)). Qed.
Lemma lem3847249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3847250 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) : (term159 _99816 s t u) = (term160 _99816 s t u).
Proof. exact (MK_COMB (@lem3847249) (@lem3847248 _99816 s t u)). Qed.
Lemma lem3847251 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term158 _99816 s t) = (term158 _99816 s t).
Proof. exact (eq_refl (term158 _99816 s t)). Qed.
Lemma lem3847252 {_99816 : Type'} (u : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term156 _99816 s t u) = (term158 _99816 s t)) = ((term154 _99816 s t u) = (term158 _99816 s t)).
Proof. exact (MK_COMB (@lem3847250 _99816 s t u) (@lem3847251 _99816 s t)). Qed.
Lemma lem3847253 {_99816 : Type'} (u : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term156 _99816 s t u) = (term157 _99816 s t)) = ((term154 _99816 s t u) = (term158 _99816 s t)).
Proof. exact (TRANS (@lem3847247 _99816 u s t) (@lem3847252 _99816 u s t)). Qed.
Lemma lem3847254 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (term154 _99816 s t u) = (term158 _99816 s t).
Proof. exact (EQ_MP (@lem3847253 _99816 u s t) (@lem3847244 _99816 s t u h1)). Qed.
Lemma lem3847256 {_99816 : Type'} : (term161 _99816) = (term161 _99816).
Proof. exact (eq_refl (term161 _99816)). Qed.
Lemma lem3847257 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (term162 _99816 u) = (term163 _99816 s t).
Proof. exact (MK_COMB (@lem3847256 _99816) (@lem3847172 _99816 s t u h1)). Qed.
Lemma lem3847258 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term163 _99816 s t) = (term164 _99816 s t).
Proof. exact (eq_refl (term163 _99816 s t)). Qed.
Lemma lem3847259 {_99816 : Type'} (u : _99816 -> Prop) : (term165 _99816 u) = (term165 _99816 u).
Proof. exact (eq_refl (term165 _99816 u)). Qed.
Lemma lem3847260 {_99816 : Type'} (u : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term162 _99816 u) = (term163 _99816 s t)) = ((term162 _99816 u) = (term164 _99816 s t)).
Proof. exact (MK_COMB (@lem3847259 _99816 u) (@lem3847258 _99816 s t)). Qed.
Lemma lem3847261 {_99816 : Type'} (u : _99816 -> Prop) : (term162 _99816 u) = (@FINITE _99816 u).
Proof. exact (eq_refl (term162 _99816 u)). Qed.
Lemma lem3847262 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3847263 {_99816 : Type'} (u : _99816 -> Prop) : (term165 _99816 u) = (term166 _99816 u).
Proof. exact (MK_COMB (@lem3847262) (@lem3847261 _99816 u)). Qed.
Lemma lem3847264 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term164 _99816 s t) = (term164 _99816 s t).
Proof. exact (eq_refl (term164 _99816 s t)). Qed.
Lemma lem3847265 {_99816 : Type'} (u : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term162 _99816 u) = (term164 _99816 s t)) = ((@FINITE _99816 u) = (term164 _99816 s t)).
Proof. exact (MK_COMB (@lem3847263 _99816 u) (@lem3847264 _99816 s t)). Qed.
Lemma lem3847266 {_99816 : Type'} (u : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term162 _99816 u) = (term163 _99816 s t)) = ((@FINITE _99816 u) = (term164 _99816 s t)).
Proof. exact (TRANS (@lem3847260 _99816 u s t) (@lem3847265 _99816 u s t)). Qed.
Lemma lem3847267 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (@FINITE _99816 u) = (term164 _99816 s t).
Proof. exact (EQ_MP (@lem3847266 _99816 u s t) (@lem3847257 _99816 s t u h1)). Qed.
Lemma lem3847282 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (@INTER _99816 s t) = (@EMPTY _99816).
Proof. exact (proj1 (@lem3846832 _99816 s t u h1)). Qed.
Lemma lem3847339 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (@EMPTY _99816) = (@INTER _99816 s t).
Proof. exact (SYM (@lem3847282 _99816 s t u h1)). Qed.
Lemma lem3847367 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term146 _99816 _44635 _44634.
Proof. exact (EQ_MP (@lem3847106 _99816 _44635 _44634) (@lem3847053 _99816 _44635 _44634 h1)). Qed.
Lemma lem3847382 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term167 _99816 _44638 _44639) = (term167 _99816 _44638 _44639).
Proof. exact (eq_refl (term167 _99816 _44638 _44639)). Qed.
Lemma lem3847383 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (term168 _99816 _44638 _44639) = (term169 _99816 _44638 _44639 s t).
Proof. exact (MK_COMB (@lem3847382 _99816 _44638 _44639) (@lem3847339 _99816 s t u h1)). Qed.
Lemma lem3847384 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term169 _99816 _44638 _44639 s t) = (term170 _99816 s t _44638 _44639).
Proof. exact (eq_refl (term169 _99816 _44638 _44639 s t)). Qed.
Lemma lem3847385 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term171 _99816 _44638 _44639) = (term171 _99816 _44638 _44639).
Proof. exact (eq_refl (term171 _99816 _44638 _44639)). Qed.
Lemma lem3847386 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : ((term168 _99816 _44638 _44639) = (term169 _99816 _44638 _44639 s t)) = ((term168 _99816 _44638 _44639) = (term170 _99816 s t _44638 _44639)).
Proof. exact (MK_COMB (@lem3847385 _99816 _44638 _44639) (@lem3847384 _99816 s t _44638 _44639)). Qed.
Lemma lem3847387 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term168 _99816 _44638 _44639) = (term153 _99816 _44638 _44639).
Proof. exact (eq_refl (term168 _99816 _44638 _44639)). Qed.
Lemma lem3847388 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3847389 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term171 _99816 _44638 _44639) = (term172 _99816 _44638 _44639).
Proof. exact (MK_COMB (@lem3847388) (@lem3847387 _99816 _44638 _44639)). Qed.
Lemma lem3847390 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term170 _99816 s t _44638 _44639) = (term170 _99816 s t _44638 _44639).
Proof. exact (eq_refl (term170 _99816 s t _44638 _44639)). Qed.
Lemma lem3847391 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : ((term168 _99816 _44638 _44639) = (term170 _99816 s t _44638 _44639)) = ((term153 _99816 _44638 _44639) = (term170 _99816 s t _44638 _44639)).
Proof. exact (MK_COMB (@lem3847389 _99816 _44638 _44639) (@lem3847390 _99816 s t _44638 _44639)). Qed.
Lemma lem3847392 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : ((term168 _99816 _44638 _44639) = (term169 _99816 _44638 _44639 s t)) = ((term153 _99816 _44638 _44639) = (term170 _99816 s t _44638 _44639)).
Proof. exact (TRANS (@lem3847386 _99816 s t _44638 _44639) (@lem3847391 _99816 s t _44638 _44639)). Qed.
Lemma lem3847393 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : (term153 _99816 _44638 _44639) = (term170 _99816 s t _44638 _44639).
Proof. exact (EQ_MP (@lem3847392 _99816 s t _44638 _44639) (@lem3847383 _99816 _44638 _44639 s t u h1)). Qed.
Lemma lem3847394 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term11 _99816) (h2 : term61 _99816 s t u) : term170 _99816 s t _44638 _44639.
Proof. exact (EQ_MP (@lem3847393 _99816 _44638 _44639 s t u h2) (@lem3847228 _99816 _44638 _44639 h1)). Qed.
Lemma lem3847422 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term158 _99816 s t.
Proof. exact (EQ_MP (@lem3847254 _99816 s t u h1) (@lem3847157 _99816 s t u h1)). Qed.
Lemma lem3847647 (x : nat) (y : nat) (z : nat) : term173 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem3847653 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term164 _99816 s t.
Proof. exact (EQ_MP (@lem3847267 _99816 s t u h1) (@lem3847159 _99816 s t u h1)). Qed.
Lemma lem3847654 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term174 _99816 s t.
Proof. exact (fun h0 : term175 _99816 s t => @lem3847653 _99816 s t u h1). Qed.
Lemma lem3847656 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847657 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term174 _99816 s t) = (term164 _99816 s t).
Proof. exact (@lem3847656 (term164 _99816 s t)). Qed.
Lemma lem3847658 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term164 _99816 s t.
Proof. exact (EQ_MP (@lem3847657 _99816 s t) (@lem3847654 _99816 s t u h1)). Qed.
Lemma lem3847660 {_99816 : Type'} (_44646 : _99816 -> Prop) (_44647 : _99816 -> Prop) (h1 : term13 _99816) : term48 _99816 _44646 _44647.
Proof. exact (EQ_MP (@lem3847088 _99816 _44646 _44647) (@lem3847087 _99816 _44646 _44647 h1)). Qed.
Lemma lem3847661 {_99816 : Type'} (_44646 : _99816 -> Prop) (_44647 : _99816 -> Prop) (h1 : term13 _99816) : term48 _99816 _44646 _44647.
Proof. exact (@lem3847660 _99816 _44646 _44647 h1). Qed.
Lemma lem3847662 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term13 _99816) : term48 _99816 s t.
Proof. exact (@lem3847661 _99816 s t h1). Qed.
Lemma lem3847663 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term13 _99816) : term177 _99816 s t.
Proof. exact (fun h0 : term178 _99816 s t => @lem3847662 _99816 s t h1). Qed.
Lemma lem3847665 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847666 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term177 _99816 s t) = (term48 _99816 s t).
Proof. exact (@lem3847665 (term48 _99816 s t)). Qed.
Lemma lem3847667 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term13 _99816) : term48 _99816 s t.
Proof. exact (EQ_MP (@lem3847666 _99816 s t) (@lem3847663 _99816 s t h1)). Qed.
Lemma lem3847683 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3847684 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term179 _99816 _44635 _44634) = (term180 _99816 _44634 _44635).
Proof. exact (@lem3847683 (@FINITE _99816 _44634) (term148 _99816 _44634 _44635)). Qed.
Lemma lem3847690 {_99816 : Type'} (_44635 : _99816 -> Prop) : (term120 _99816 _44635) = (term120 _99816 _44635).
Proof. exact (eq_refl (term120 _99816 _44635)). Qed.
Lemma lem3847691 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term146 _99816 _44635 _44634) = (term181 _99816 _44634 _44635).
Proof. exact (MK_COMB (@lem3847690 _99816 _44635) (@lem3847684 _99816 _44634 _44635)). Qed.
Lemma lem3847695 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3847696 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term181 _99816 _44634 _44635) = (term182 _99816 _44634 _44635).
Proof. exact (@lem3847695 (@FINITE _99816 _44634) (term147 _99816 _44635) (term148 _99816 _44634 _44635)). Qed.
Lemma lem3847712 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term146 _99816 _44635 _44634) = (term182 _99816 _44634 _44635).
Proof. exact (TRANS (@lem3847691 _99816 _44634 _44635) (@lem3847696 _99816 _44634 _44635)). Qed.
Lemma lem3847713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3847714 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term183 _99816 _44635 _44634) = (term184 _99816 _44634 _44635).
Proof. exact (MK_COMB (@lem3847713) (@lem3847712 _99816 _44634 _44635)). Qed.
Lemma lem3847730 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term182 _99816 _44634 _44635) = (term182 _99816 _44634 _44635).
Proof. exact (eq_refl (term182 _99816 _44634 _44635)). Qed.
Lemma lem3847731 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : ((term146 _99816 _44635 _44634) = (term182 _99816 _44634 _44635)) = ((term182 _99816 _44634 _44635) = (term182 _99816 _44634 _44635)).
Proof. exact (MK_COMB (@lem3847714 _99816 _44634 _44635) (@lem3847730 _99816 _44634 _44635)). Qed.
Lemma lem3847733 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3847734 (x : Prop) : (x = x) = True.
Proof. exact (@lem3847733 Prop x). Qed.
Lemma lem3847735 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : ((term182 _99816 _44634 _44635) = (term182 _99816 _44634 _44635)) = True.
Proof. exact (@lem3847734 (term182 _99816 _44634 _44635)). Qed.
Lemma lem3847736 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : ((term146 _99816 _44635 _44634) = (term182 _99816 _44634 _44635)) = True.
Proof. exact (TRANS (@lem3847731 _99816 _44634 _44635) (@lem3847735 _99816 _44634 _44635)). Qed.
Lemma lem3847737 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : True = ((term146 _99816 _44635 _44634) = (term182 _99816 _44634 _44635)).
Proof. exact (SYM (@lem3847736 _99816 _44634 _44635)). Qed.
Lemma lem3847738 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term146 _99816 _44635 _44634) = (term182 _99816 _44634 _44635).
Proof. exact (EQ_MP (@lem3847737 _99816 _44634 _44635) (@lem0)). Qed.
Lemma lem3847739 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) (h1 : term12 _99816) : term182 _99816 _44634 _44635.
Proof. exact (EQ_MP (@lem3847738 _99816 _44634 _44635) (@lem3847367 _99816 _44635 _44634 h1)). Qed.
Lemma lem3847741 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3847742 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) : (term182 _99816 _44634 _44635) = (term186 _99816 _44635 _44634).
Proof. exact (@lem3847741 (term87 _99816 _44634 _44635) (@FINITE _99816 _44634)). Qed.
Lemma lem3847744 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3847745 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term189 _99816 _44634 _44635) = (term190 _99816 _44634 _44635).
Proof. exact (@lem3847744 (term147 _99816 _44635) (term148 _99816 _44634 _44635)). Qed.
Lemma lem3847747 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3847748 {_99816 : Type'} (_44635 : _99816 -> Prop) : (term192 _99816 _44635) = (@FINITE _99816 _44635).
Proof. exact (@lem3847747 (@FINITE _99816 _44635)). Qed.
Lemma lem3847749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3847750 {_99816 : Type'} (_44635 : _99816 -> Prop) : (term193 _99816 _44635) = (term194 _99816 _44635).
Proof. exact (MK_COMB (@lem3847749) (@lem3847748 _99816 _44635)). Qed.
Lemma lem3847752 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3847753 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term195 _99816 _44634 _44635) = (@SUBSET _99816 _44634 _44635).
Proof. exact (@lem3847752 (@SUBSET _99816 _44634 _44635)). Qed.
Lemma lem3847754 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term190 _99816 _44634 _44635) = (term92 _99816 _44634 _44635).
Proof. exact (MK_COMB (@lem3847750 _99816 _44635) (@lem3847753 _99816 _44634 _44635)). Qed.
Lemma lem3847755 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term189 _99816 _44634 _44635) = (term92 _99816 _44634 _44635).
Proof. exact (TRANS (@lem3847745 _99816 _44634 _44635) (@lem3847754 _99816 _44634 _44635)). Qed.
Lemma lem3847756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3847757 {_99816 : Type'} (_44634 : _99816 -> Prop) (_44635 : _99816 -> Prop) : (term196 _99816 _44634 _44635) = (term197 _99816 _44634 _44635).
Proof. exact (MK_COMB (@lem3847756) (@lem3847755 _99816 _44634 _44635)). Qed.
Lemma lem3847758 {_99816 : Type'} (_44634 : _99816 -> Prop) : (@FINITE _99816 _44634) = (@FINITE _99816 _44634).
Proof. exact (eq_refl (@FINITE _99816 _44634)). Qed.
Lemma lem3847759 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) : (term186 _99816 _44635 _44634) = (term39 _99816 _44635 _44634).
Proof. exact (MK_COMB (@lem3847757 _99816 _44634 _44635) (@lem3847758 _99816 _44634)). Qed.
Lemma lem3847760 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) : (term182 _99816 _44634 _44635) = (term39 _99816 _44635 _44634).
Proof. exact (TRANS (@lem3847742 _99816 _44635 _44634) (@lem3847759 _99816 _44635 _44634)). Qed.
Lemma lem3847762 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term13 _99816) (h2 : term61 _99816 s t u) : term198 _99816 s t.
Proof. exact (conj (@lem3847658 _99816 s t u h2) (@lem3847667 _99816 s t h1)). Qed.
Lemma lem3847764 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term39 _99816 _44635 _44634.
Proof. exact (EQ_MP (@lem3847760 _99816 _44635 _44634) (@lem3847739 _99816 _44634 _44635 h1)). Qed.
Lemma lem3847765 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term39 _99816 _44635 _44634.
Proof. exact (@lem3847764 _99816 _44635 _44634 h1). Qed.
Lemma lem3847766 {_99816 : Type'} (t : _99816 -> Prop) (s : _99816 -> Prop) (h1 : term12 _99816) : term199 _99816 t s.
Proof. exact (@lem3847765 _99816 (@UNION _99816 s t) s h1). Qed.
Lemma lem3847769 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : @FINITE _99816 s.
Proof. exact (@lem3847766 _99816 t s h1 (@lem3847762 _99816 s t u h2 h3)). Qed.
Lemma lem3847770 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : term200 _99816 s.
Proof. exact (fun h0 : term147 _99816 s => @lem3847769 _99816 s t u h1 h2 h3). Qed.
Lemma lem3847772 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847773 {_99816 : Type'} (s : _99816 -> Prop) : (term200 _99816 s) = (@FINITE _99816 s).
Proof. exact (@lem3847772 (@FINITE _99816 s)). Qed.
Lemma lem3847774 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : @FINITE _99816 s.
Proof. exact (EQ_MP (@lem3847773 _99816 s) (@lem3847770 _99816 s t u h1 h2 h3)). Qed.
Lemma lem3847776 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term164 _99816 s t.
Proof. exact (EQ_MP (@lem3847267 _99816 s t u h1) (@lem3847159 _99816 s t u h1)). Qed.
Lemma lem3847777 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term174 _99816 s t.
Proof. exact (fun h0 : term175 _99816 s t => @lem3847776 _99816 s t u h1). Qed.
Lemma lem3847779 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847780 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term174 _99816 s t) = (term164 _99816 s t).
Proof. exact (@lem3847779 (term164 _99816 s t)). Qed.
Lemma lem3847781 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term164 _99816 s t.
Proof. exact (EQ_MP (@lem3847780 _99816 s t) (@lem3847777 _99816 s t u h1)). Qed.
Lemma lem3847783 {_99816 : Type'} (_44649 : _99816 -> Prop) (_44648 : _99816 -> Prop) (h1 : term13 _99816) : term43 _99816 _44649 _44648.
Proof. exact (EQ_MP (@lem3847094 _99816 _44649 _44648) (@lem3847093 _99816 _44648 _44649 h1)). Qed.
Lemma lem3847784 {_99816 : Type'} (_44649 : _99816 -> Prop) (_44648 : _99816 -> Prop) (h1 : term13 _99816) : term43 _99816 _44649 _44648.
Proof. exact (@lem3847783 _99816 _44649 _44648 h1). Qed.
Lemma lem3847785 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term13 _99816) : term43 _99816 s t.
Proof. exact (@lem3847784 _99816 s t h1). Qed.
Lemma lem3847786 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term13 _99816) : term201 _99816 s t.
Proof. exact (fun h0 : term202 _99816 s t => @lem3847785 _99816 s t h1). Qed.
Lemma lem3847788 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847789 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term201 _99816 s t) = (term43 _99816 s t).
Proof. exact (@lem3847788 (term43 _99816 s t)). Qed.
Lemma lem3847790 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term13 _99816) : term43 _99816 s t.
Proof. exact (EQ_MP (@lem3847789 _99816 s t) (@lem3847786 _99816 s t h1)). Qed.
Lemma lem3847791 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term13 _99816) (h2 : term61 _99816 s t u) : term203 _99816 s t.
Proof. exact (conj (@lem3847781 _99816 s t u h2) (@lem3847790 _99816 s t h1)). Qed.
Lemma lem3847793 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term39 _99816 _44635 _44634.
Proof. exact (EQ_MP (@lem3847760 _99816 _44635 _44634) (@lem3847739 _99816 _44634 _44635 h1)). Qed.
Lemma lem3847794 {_99816 : Type'} (_44635 : _99816 -> Prop) (_44634 : _99816 -> Prop) (h1 : term12 _99816) : term39 _99816 _44635 _44634.
Proof. exact (@lem3847793 _99816 _44635 _44634 h1). Qed.
Lemma lem3847795 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term12 _99816) : term204 _99816 s t.
Proof. exact (@lem3847794 _99816 (@UNION _99816 s t) t h1). Qed.
Lemma lem3847798 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : @FINITE _99816 t.
Proof. exact (@lem3847795 _99816 s t h1 (@lem3847791 _99816 s t u h2 h3)). Qed.
Lemma lem3847799 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : term200 _99816 t.
Proof. exact (fun h0 : term147 _99816 t => @lem3847798 _99816 s t u h1 h2 h3). Qed.
Lemma lem3847801 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847802 {_99816 : Type'} (t : _99816 -> Prop) : (term200 _99816 t) = (@FINITE _99816 t).
Proof. exact (@lem3847801 (@FINITE _99816 t)). Qed.
Lemma lem3847803 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : @FINITE _99816 t.
Proof. exact (EQ_MP (@lem3847802 _99816 t) (@lem3847799 _99816 s t u h1 h2 h3)). Qed.
Lemma lem3847805 {_99816 : Type'} (x : _99816 -> Prop) : x = x.
Proof. exact (@lem21386 (_99816 -> Prop) x). Qed.
Lemma lem3847806 {_99816 : Type'} (x : _99816 -> Prop) : x = x.
Proof. exact (@lem3847805 _99816 x). Qed.
Lemma lem3847807 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (@INTER _99816 s t) = (@INTER _99816 s t).
Proof. exact (@lem3847806 _99816 (@INTER _99816 s t)). Qed.
Lemma lem3847808 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term205 _99816 s t.
Proof. exact (fun h0 : term206 _99816 s t => @lem3847807 _99816 s t). Qed.
Lemma lem3847810 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3847811 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term205 _99816 s t) = ((@INTER _99816 s t) = (@INTER _99816 s t)).
Proof. exact (@lem3847810 ((@INTER _99816 s t) = (@INTER _99816 s t))). Qed.
Lemma lem3847812 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (@INTER _99816 s t) = (@INTER _99816 s t).
Proof. exact (EQ_MP (@lem3847811 _99816 s t) (@lem3847808 _99816 s t)). Qed.
Lemma lem3847828 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3847829 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term207 _99816 s t _44638 _44639) = (term208 _99816 s t _44638 _44639).
Proof. exact (@lem3847828 (term209 _99816 _44638 _44639 s t) (term147 _99816 _44639) ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639))). Qed.
Lemma lem3847845 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3847846 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term210 _99816 _44638 _44639) = (term211 _99816 _44638 _44639).
Proof. exact (@lem3847845 ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639)) (term147 _99816 _44639)). Qed.
Lemma lem3847854 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term212 _99816 _44638 _44639 s t) = (term212 _99816 _44638 _44639 s t).
Proof. exact (eq_refl (term212 _99816 _44638 _44639 s t)). Qed.
Lemma lem3847855 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term208 _99816 s t _44638 _44639) = (term213 _99816 s t _44638 _44639).
Proof. exact (MK_COMB (@lem3847854 _99816 _44638 _44639 s t) (@lem3847846 _99816 _44638 _44639)). Qed.
Lemma lem3847859 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3847860 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term213 _99816 s t _44638 _44639) = (term214 _99816 _44638 s t _44639).
Proof. exact (@lem3847859 ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639)) (term209 _99816 _44638 _44639 s t) (term147 _99816 _44639)). Qed.
Lemma lem3847880 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term208 _99816 s t _44638 _44639) = (term214 _99816 _44638 s t _44639).
Proof. exact (TRANS (@lem3847855 _99816 s t _44638 _44639) (@lem3847860 _99816 _44638 s t _44639)). Qed.
Lemma lem3847881 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term207 _99816 s t _44638 _44639) = (term214 _99816 _44638 s t _44639).
Proof. exact (TRANS (@lem3847829 _99816 s t _44638 _44639) (@lem3847880 _99816 _44638 s t _44639)). Qed.
Lemma lem3847882 {_99816 : Type'} (_44638 : _99816 -> Prop) : (term120 _99816 _44638) = (term120 _99816 _44638).
Proof. exact (eq_refl (term120 _99816 _44638)). Qed.
Lemma lem3847883 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term170 _99816 s t _44638 _44639) = (term215 _99816 _44638 s t _44639).
Proof. exact (MK_COMB (@lem3847882 _99816 _44638) (@lem3847881 _99816 _44638 s t _44639)). Qed.
Lemma lem3847887 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3847888 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term215 _99816 _44638 s t _44639) = (term216 _99816 _44638 s t _44639).
Proof. exact (@lem3847887 ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639)) (term147 _99816 _44638) (term217 _99816 _44638 s t _44639)). Qed.
Lemma lem3847904 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3847905 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term218 _99816 _44638 s t _44639) = (term219 _99816 s t _44638 _44639).
Proof. exact (@lem3847904 (term209 _99816 _44638 _44639 s t) (term147 _99816 _44638) (term147 _99816 _44639)). Qed.
Lemma lem3847923 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term220 _99816 _44638 _44639) = (term220 _99816 _44638 _44639).
Proof. exact (eq_refl (term220 _99816 _44638 _44639)). Qed.
Lemma lem3847924 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term216 _99816 _44638 s t _44639) = (term221 _99816 s t _44638 _44639).
Proof. exact (MK_COMB (@lem3847923 _99816 _44638 _44639) (@lem3847905 _99816 s t _44638 _44639)). Qed.
Lemma lem3847935 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term215 _99816 _44638 s t _44639) = (term221 _99816 s t _44638 _44639).
Proof. exact (TRANS (@lem3847888 _99816 _44638 s t _44639) (@lem3847924 _99816 s t _44638 _44639)). Qed.
Lemma lem3847936 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term170 _99816 s t _44638 _44639) = (term221 _99816 s t _44638 _44639).
Proof. exact (TRANS (@lem3847883 _99816 _44638 s t _44639) (@lem3847935 _99816 s t _44638 _44639)). Qed.
Lemma lem3847937 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3847938 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term222 _99816 s t _44638 _44639) = (term223 _99816 s t _44638 _44639).
Proof. exact (MK_COMB (@lem3847937) (@lem3847936 _99816 s t _44638 _44639)). Qed.
Lemma lem3847964 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3847965 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term224 _99816 _44638 _44639 s t) = (term217 _99816 _44638 s t _44639).
Proof. exact (@lem3847964 (term209 _99816 _44638 _44639 s t) (term147 _99816 _44639)). Qed.
Lemma lem3847973 {_99816 : Type'} (_44638 : _99816 -> Prop) : (term120 _99816 _44638) = (term120 _99816 _44638).
Proof. exact (eq_refl (term120 _99816 _44638)). Qed.
Lemma lem3847974 {_99816 : Type'} (_44638 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term225 _99816 _44638 _44639 s t) = (term218 _99816 _44638 s t _44639).
Proof. exact (MK_COMB (@lem3847973 _99816 _44638) (@lem3847965 _99816 _44638 s t _44639)). Qed.
Lemma lem3847978 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3847979 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term218 _99816 _44638 s t _44639) = (term219 _99816 s t _44638 _44639).
Proof. exact (@lem3847978 (term209 _99816 _44638 _44639 s t) (term147 _99816 _44638) (term147 _99816 _44639)). Qed.
Lemma lem3847997 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term225 _99816 _44638 _44639 s t) = (term219 _99816 s t _44638 _44639).
Proof. exact (TRANS (@lem3847974 _99816 _44638 s t _44639) (@lem3847979 _99816 s t _44638 _44639)). Qed.
Lemma lem3847998 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term220 _99816 _44638 _44639) = (term220 _99816 _44638 _44639).
Proof. exact (eq_refl (term220 _99816 _44638 _44639)). Qed.
Lemma lem3847999 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term226 _99816 _44638 _44639 s t) = (term221 _99816 s t _44638 _44639).
Proof. exact (MK_COMB (@lem3847998 _99816 _44638 _44639) (@lem3847997 _99816 s t _44638 _44639)). Qed.
Lemma lem3848010 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : ((term170 _99816 s t _44638 _44639) = (term226 _99816 _44638 _44639 s t)) = ((term221 _99816 s t _44638 _44639) = (term221 _99816 s t _44638 _44639)).
Proof. exact (MK_COMB (@lem3847938 _99816 s t _44638 _44639) (@lem3847999 _99816 s t _44638 _44639)). Qed.
Lemma lem3848012 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3848013 (x : Prop) : (x = x) = True.
Proof. exact (@lem3848012 Prop x). Qed.
Lemma lem3848014 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : ((term221 _99816 s t _44638 _44639) = (term221 _99816 s t _44638 _44639)) = True.
Proof. exact (@lem3848013 (term221 _99816 s t _44638 _44639)). Qed.
Lemma lem3848015 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : ((term170 _99816 s t _44638 _44639) = (term226 _99816 _44638 _44639 s t)) = True.
Proof. exact (TRANS (@lem3848010 _99816 s t _44638 _44639) (@lem3848014 _99816 s t _44638 _44639)). Qed.
Lemma lem3848016 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : True = ((term170 _99816 s t _44638 _44639) = (term226 _99816 _44638 _44639 s t)).
Proof. exact (SYM (@lem3848015 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848017 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term170 _99816 s t _44638 _44639) = (term226 _99816 _44638 _44639 s t).
Proof. exact (EQ_MP (@lem3848016 _99816 _44638 _44639 s t) (@lem0)). Qed.
Lemma lem3848018 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term11 _99816) (h2 : term61 _99816 s t u) : term226 _99816 _44638 _44639 s t.
Proof. exact (EQ_MP (@lem3848017 _99816 _44638 _44639 s t) (@lem3847394 _99816 _44638 _44639 s t u h1 h2)). Qed.
Lemma lem3848020 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3848021 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term226 _99816 _44638 _44639 s t) = (term227 _99816 s t _44638 _44639).
Proof. exact (@lem3848020 (term225 _99816 _44638 _44639 s t) ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639))). Qed.
Lemma lem3848023 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3848024 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term228 _99816 _44638 _44639 s t) = (term229 _99816 _44638 _44639 s t).
Proof. exact (@lem3848023 (term147 _99816 _44638) (term224 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848026 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3848027 {_99816 : Type'} (_44638 : _99816 -> Prop) : (term192 _99816 _44638) = (@FINITE _99816 _44638).
Proof. exact (@lem3848026 (@FINITE _99816 _44638)). Qed.
Lemma lem3848028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848029 {_99816 : Type'} (_44638 : _99816 -> Prop) : (term193 _99816 _44638) = (term194 _99816 _44638).
Proof. exact (MK_COMB (@lem3848028) (@lem3848027 _99816 _44638)). Qed.
Lemma lem3848031 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3848032 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term230 _99816 _44638 _44639 s t) = (term231 _99816 _44638 _44639 s t).
Proof. exact (@lem3848031 (term147 _99816 _44639) (term209 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848034 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3848035 {_99816 : Type'} (_44639 : _99816 -> Prop) : (term192 _99816 _44639) = (@FINITE _99816 _44639).
Proof. exact (@lem3848034 (@FINITE _99816 _44639)). Qed.
Lemma lem3848036 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848037 {_99816 : Type'} (_44639 : _99816 -> Prop) : (term193 _99816 _44639) = (term194 _99816 _44639).
Proof. exact (MK_COMB (@lem3848036) (@lem3848035 _99816 _44639)). Qed.
Lemma lem3848039 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3848040 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term232 _99816 _44638 _44639 s t) = ((@INTER _99816 _44638 _44639) = (@INTER _99816 s t)).
Proof. exact (@lem3848039 ((@INTER _99816 _44638 _44639) = (@INTER _99816 s t))). Qed.
Lemma lem3848041 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term231 _99816 _44638 _44639 s t) = (term233 _99816 _44638 _44639 s t).
Proof. exact (MK_COMB (@lem3848037 _99816 _44639) (@lem3848040 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848042 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term230 _99816 _44638 _44639 s t) = (term233 _99816 _44638 _44639 s t).
Proof. exact (TRANS (@lem3848032 _99816 _44638 _44639 s t) (@lem3848041 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848043 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term229 _99816 _44638 _44639 s t) = (term234 _99816 _44638 _44639 s t).
Proof. exact (MK_COMB (@lem3848029 _99816 _44638) (@lem3848042 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848044 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term228 _99816 _44638 _44639 s t) = (term234 _99816 _44638 _44639 s t).
Proof. exact (TRANS (@lem3848024 _99816 _44638 _44639 s t) (@lem3848043 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848045 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3848046 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) : (term235 _99816 _44638 _44639 s t) = (term236 _99816 _44638 _44639 s t).
Proof. exact (MK_COMB (@lem3848045) (@lem3848044 _99816 _44638 _44639 s t)). Qed.
Lemma lem3848047 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639)) = ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639)).
Proof. exact (eq_refl ((term125 _99816 _44638 _44639) = (term63 _99816 _44638 _44639))). Qed.
Lemma lem3848048 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term227 _99816 s t _44638 _44639) = (term237 _99816 s t _44638 _44639).
Proof. exact (MK_COMB (@lem3848046 _99816 _44638 _44639 s t) (@lem3848047 _99816 _44638 _44639)). Qed.
Lemma lem3848049 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) : (term226 _99816 _44638 _44639 s t) = (term237 _99816 s t _44638 _44639).
Proof. exact (TRANS (@lem3848021 _99816 s t _44638 _44639) (@lem3848048 _99816 s t _44638 _44639)). Qed.
Lemma lem3848051 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : term238 _99816 s t.
Proof. exact (conj (@lem3847803 _99816 s t u h1 h2 h3) (@lem3847812 _99816 s t)). Qed.
Lemma lem3848052 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term13 _99816) (h3 : term61 _99816 s t u) : term239 _99816 s t.
Proof. exact (conj (@lem3847774 _99816 s t u h1 h2 h3) (@lem3848051 _99816 s t u h1 h2 h3)). Qed.
Lemma lem3848054 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term11 _99816) (h2 : term61 _99816 s t u) : term237 _99816 s t _44638 _44639.
Proof. exact (EQ_MP (@lem3848049 _99816 s t _44638 _44639) (@lem3848018 _99816 _44638 _44639 s t u h1 h2)). Qed.
Lemma lem3848055 {_99816 : Type'} (_44638 : _99816 -> Prop) (_44639 : _99816 -> Prop) (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term11 _99816) (h2 : term61 _99816 s t u) : term237 _99816 s t _44638 _44639.
Proof. exact (@lem3848054 _99816 _44638 _44639 s t u h1 h2). Qed.
Lemma lem3848056 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term11 _99816) (h2 : term61 _99816 s t u) : term240 _99816 s t.
Proof. exact (@lem3848055 _99816 s t s t u h1 h2). Qed.
Lemma lem3848059 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : (term125 _99816 s t) = (term63 _99816 s t).
Proof. exact (@lem3848056 _99816 s t u h2 h4 (@lem3848052 _99816 s t u h1 h3 h4)). Qed.
Lemma lem3848060 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : term241 _99816 s t.
Proof. exact (fun h0 : term242 _99816 s t => @lem3848059 _99816 s t u h1 h2 h3 h4). Qed.
Lemma lem3848062 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3848063 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term241 _99816 s t) = ((term125 _99816 s t) = (term63 _99816 s t)).
Proof. exact (@lem3848062 ((term125 _99816 s t) = (term63 _99816 s t))). Qed.
Lemma lem3848064 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : (term125 _99816 s t) = (term63 _99816 s t).
Proof. exact (EQ_MP (@lem3848063 _99816 s t) (@lem3848060 _99816 s t u h1 h2 h3 h4)). Qed.
Lemma lem3848066 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem3848067 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term125 _99816 s t) = (term125 _99816 s t).
Proof. exact (@lem3848066 (term125 _99816 s t)). Qed.
Lemma lem3848068 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term243 _99816 s t.
Proof. exact (fun h0 : term244 _99816 s t => @lem3848067 _99816 s t). Qed.
Lemma lem3848070 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3848071 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term243 _99816 s t) = ((term125 _99816 s t) = (term125 _99816 s t)).
Proof. exact (@lem3848070 ((term125 _99816 s t) = (term125 _99816 s t))). Qed.
Lemma lem3848072 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term125 _99816 s t) = (term125 _99816 s t).
Proof. exact (EQ_MP (@lem3848071 _99816 s t) (@lem3848068 _99816 s t)). Qed.
Lemma lem3848090 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3848091 (y : nat) (x : nat) (z : nat) : (term245 x y z) = (term246 y x z).
Proof. exact (@lem3848090 (y = z) (term247 x z)). Qed.
Lemma lem3848101 (x : nat) (y : nat) : (term248 x y) = (term248 x y).
Proof. exact (eq_refl (term248 x y)). Qed.
Lemma lem3848102 (y : nat) (x : nat) (z : nat) : (term173 x y z) = (term249 y x z).
Proof. exact (MK_COMB (@lem3848101 x y) (@lem3848091 y x z)). Qed.
Lemma lem3848106 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3848107 (y : nat) (x : nat) (z : nat) : (term249 y x z) = (term250 y x z).
Proof. exact (@lem3848106 (y = z) (term247 x y) (term247 x z)). Qed.
Lemma lem3848129 (y : nat) (x : nat) (z : nat) : (term173 x y z) = (term250 y x z).
Proof. exact (TRANS (@lem3848102 y x z) (@lem3848107 y x z)). Qed.
Lemma lem3848130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3848131 (y : nat) (x : nat) (z : nat) : (term251 x y z) = (term252 y x z).
Proof. exact (MK_COMB (@lem3848130) (@lem3848129 y x z)). Qed.
Lemma lem3848153 (y : nat) (x : nat) (z : nat) : (term250 y x z) = (term250 y x z).
Proof. exact (eq_refl (term250 y x z)). Qed.
Lemma lem3848154 (y : nat) (x : nat) (z : nat) : ((term173 x y z) = (term250 y x z)) = ((term250 y x z) = (term250 y x z)).
Proof. exact (MK_COMB (@lem3848131 y x z) (@lem3848153 y x z)). Qed.
Lemma lem3848156 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3848157 (x : Prop) : (x = x) = True.
Proof. exact (@lem3848156 Prop x). Qed.
Lemma lem3848158 (y : nat) (x : nat) (z : nat) : ((term250 y x z) = (term250 y x z)) = True.
Proof. exact (@lem3848157 (term250 y x z)). Qed.
Lemma lem3848159 (y : nat) (x : nat) (z : nat) : ((term173 x y z) = (term250 y x z)) = True.
Proof. exact (TRANS (@lem3848154 y x z) (@lem3848158 y x z)). Qed.
Lemma lem3848160 (y : nat) (x : nat) (z : nat) : True = ((term173 x y z) = (term250 y x z)).
Proof. exact (SYM (@lem3848159 y x z)). Qed.
Lemma lem3848161 (y : nat) (x : nat) (z : nat) : (term173 x y z) = (term250 y x z).
Proof. exact (EQ_MP (@lem3848160 y x z) (@lem0)). Qed.
Lemma lem3848162 (y : nat) (x : nat) (z : nat) : term250 y x z.
Proof. exact (EQ_MP (@lem3848161 y x z) (@lem3847647 x y z)). Qed.
Lemma lem3848164 (b : Prop) (a : Prop) : (a \/ b) = (term185 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3848165 (x : nat) (y : nat) (z : nat) : (term250 y x z) = (term253 x y z).
Proof. exact (@lem3848164 (term254 y x z) (y = z)). Qed.
Lemma lem3848167 (a : Prop) (b : Prop) : (term187 a b) = (term188 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3848168 (y : nat) (x : nat) (z : nat) : (term255 y x z) = (term256 y x z).
Proof. exact (@lem3848167 (term247 x y) (term247 x z)). Qed.
Lemma lem3848170 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3848171 (x : nat) (y : nat) : (term257 x y) = (x = y).
Proof. exact (@lem3848170 (x = y)). Qed.
Lemma lem3848172 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3848173 (x : nat) (y : nat) : (term258 x y) = (term259 x y).
Proof. exact (MK_COMB (@lem3848172) (@lem3848171 x y)). Qed.
Lemma lem3848175 (a : Prop) : (term191 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3848176 (x : nat) (z : nat) : (term257 x z) = (x = z).
Proof. exact (@lem3848175 (x = z)). Qed.
Lemma lem3848177 (y : nat) (x : nat) (z : nat) : (term256 y x z) = (term260 y x z).
Proof. exact (MK_COMB (@lem3848173 x y) (@lem3848176 x z)). Qed.
Lemma lem3848178 (y : nat) (x : nat) (z : nat) : (term255 y x z) = (term260 y x z).
Proof. exact (TRANS (@lem3848168 y x z) (@lem3848177 y x z)). Qed.
Lemma lem3848179 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3848180 (y : nat) (x : nat) (z : nat) : (term261 y x z) = (term262 y x z).
Proof. exact (MK_COMB (@lem3848179) (@lem3848178 y x z)). Qed.
Lemma lem3848181 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3848182 (x : nat) (y : nat) (z : nat) : (term253 x y z) = (term263 x y z).
Proof. exact (MK_COMB (@lem3848180 y x z) (@lem3848181 y z)). Qed.
Lemma lem3848183 (x : nat) (y : nat) (z : nat) : (term250 y x z) = (term263 x y z).
Proof. exact (TRANS (@lem3848165 x y z) (@lem3848182 x y z)). Qed.
Lemma lem3848185 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : term264 _99816 s t.
Proof. exact (conj (@lem3848064 _99816 s t u h1 h2 h3 h4) (@lem3848072 _99816 s t)). Qed.
Lemma lem3848187 (x : nat) (y : nat) (z : nat) : term263 x y z.
Proof. exact (EQ_MP (@lem3848183 x y z) (@lem3848162 y x z)). Qed.
Lemma lem3848188 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : term265 _99816 s t.
Proof. exact (@lem3848187 (term125 _99816 s t) (term63 _99816 s t) (term125 _99816 s t)). Qed.
Lemma lem3848191 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : (term63 _99816 s t) = (term125 _99816 s t).
Proof. exact (@lem3848188 _99816 s t (@lem3848185 _99816 s t u h1 h2 h3 h4)). Qed.
Lemma lem3848192 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : term266 _99816 s t.
Proof. exact (fun h0 : term158 _99816 s t => @lem3848191 _99816 s t u h1 h2 h3 h4). Qed.
Lemma lem3848194 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3848195 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term266 _99816 s t) = ((term63 _99816 s t) = (term125 _99816 s t)).
Proof. exact (@lem3848194 ((term63 _99816 s t) = (term125 _99816 s t))). Qed.
Lemma lem3848196 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : (term63 _99816 s t) = (term125 _99816 s t).
Proof. exact (EQ_MP (@lem3848195 _99816 s t) (@lem3848192 _99816 s t u h1 h2 h3 h4)). Qed.
Lemma lem3848199 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3848201 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) : (term158 _99816 s t) = (term267 _99816 s t).
Proof. exact (@lem3848199 ((term63 _99816 s t) = (term125 _99816 s t))). Qed.
Lemma lem3848204 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term61 _99816 s t u) : term267 _99816 s t.
Proof. exact (EQ_MP (@lem3848201 _99816 s t) (@lem3847422 _99816 s t u h1)). Qed.
Lemma lem3848207 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : False.
Proof. exact (@lem3848204 _99816 s t u h4 (@lem3848196 _99816 s t u h1 h2 h3 h4)). Qed.
Lemma lem3848208 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : term268.
Proof. exact (fun h0 : ~ False => @lem3848207 _99816 s t u h1 h2 h3 h4). Qed.
Lemma lem3848210 (p : Prop) : (term176 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3848211 : term268 = False.
Proof. exact (@lem3848210 False). Qed.
Lemma lem3848214 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : False.
Proof. exact (EQ_MP (@lem3848211) (@lem3848208 _99816 s t u h1 h2 h3 h4)). Qed.
Lemma lem3848215 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : (term61 _99816 s t u) = False.
Proof. exact (prop_ext (fun h5 : term61 _99816 s t u => @lem3848214 _99816 s t u h1 h2 h3 h4) (fun h5 : False => @lem3846829 _99816 s t u h4)). Qed.
Lemma lem3848216 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : False.
Proof. exact (EQ_MP (@lem3848215 _99816 s t u h1 h2 h3 h4) (@lem3846829 _99816 s t u h4)). Qed.
Lemma lem3848217 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : (term13 _99816) = False.
Proof. exact (prop_ext (fun h5 : term13 _99816 => @lem3848216 _99816 s t u h1 h2 h3 h4) (fun h5 : False => @lem3846579 _99816 h3)). Qed.
Lemma lem3848218 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (u : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term13 _99816) (h4 : term61 _99816 s t u) : False.
Proof. exact (EQ_MP (@lem3848217 _99816 s t u h1 h2 h3 h4) (@lem3846579 _99816 h3)). Qed.
Lemma lem3848219 {_99816 : Type'} (s : _99816 -> Prop) (t : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term72 _99816 s t) (h4 : term13 _99816) : False.
Proof. exact (ex_elim (@lem3846544 _99816 s t h3) (fun u : _99816 -> Prop => fun h0 : term71 _99816 s t u => @lem3848218 _99816 s t u h1 h2 h4 h0)). Qed.
Lemma lem3848220 {_99816 : Type'} (s : _99816 -> Prop) (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term79 _99816 s) (h4 : term13 _99816) : False.
Proof. exact (ex_elim (@lem3846543 _99816 s h3) (fun t : _99816 -> Prop => fun h0 : term78 _99816 s t => @lem3848219 _99816 s t h1 h2 h0 h4)). Qed.
Lemma lem3848221 {_99816 : Type'} (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term10 _99816) (h4 : term13 _99816) : False.
Proof. exact (ex_elim (@lem3845994 _99816 h3) (fun s : _99816 -> Prop => fun h0 : term84 _99816 s => @lem3848220 _99816 s h1 h2 h0 h4)). Qed.
Lemma lem3848222 {_99816 : Type'} (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term10 _99816) (h4 : term13 _99816) : (term13 _99816) = False.
Proof. exact (prop_ext (fun h5 : term13 _99816 => @lem3848221 _99816 h1 h2 h3 h4) (fun h5 : False => @lem3846032 _99816 h4)). Qed.
Lemma lem3848223 {_99816 : Type'} (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term10 _99816) (h4 : term13 _99816) : False.
Proof. exact (EQ_MP (@lem3848222 _99816 h1 h2 h3 h4) (@lem3846032 _99816 h4)). Qed.
Lemma lem3848224 {_99816 A : Type'} (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term10 _99816) (h4 : term13 _99816) : term18 A.
Proof. exact (fun h0 : term11 A => @lem3848223 _99816 h1 h2 h3 h4). Qed.
Lemma lem3848225 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (@lem69 (term11 A)). Qed.
Lemma lem3848226 {_99816 A : Type'} (h1 : term12 _99816) (h2 : term11 _99816) (h3 : term10 _99816) (h4 : term13 _99816) : term19 A.
Proof. exact (EQ_MP (@lem3848225 A) (@lem3848224 _99816 A h1 h2 h3 h4)). Qed.
Lemma lem3848227 {_99816 A : Type'} (h1 : term12 _99816) (h2 : term10 _99816) (h3 : term13 _99816) : term22 _99816 A.
Proof. exact (fun h0 : term11 _99816 => @lem3848226 _99816 A h1 h0 h2 h3). Qed.
Lemma lem3848228 {_99816 A : Type'} (h1 : term12 _99816) (h2 : term10 _99816) (h3 : term13 _99816) : term25 _99816 A.
Proof. exact (fun h0 : term12 A => @lem3848227 _99816 A h1 h2 h3). Qed.
Lemma lem3848229 {_99816 A : Type'} (h1 : term10 _99816) (h2 : term13 _99816) : term27 _99816 A.
Proof. exact (fun h0 : term12 _99816 => @lem3848228 _99816 A h0 h1 h2). Qed.
Lemma lem3848230 {_99816 A : Type'} (h1 : term10 _99816) (h2 : term13 _99816) : term30 _99816 A.
Proof. exact (fun h0 : term13 A => @lem3848229 _99816 A h1 h2). Qed.
Lemma lem3848231 {_99816 A : Type'} (h1 : term10 _99816) : term32 _99816 A.
Proof. exact (fun h0 : term13 _99816 => @lem3848230 _99816 A h1 h0). Qed.
Lemma lem3848232 {_99816 A : Type'} : term34 _99816 A.
Proof. exact (fun h0 : term10 _99816 => @lem3848231 _99816 A h0). Qed.
Lemma lem3848233 {_99816 A : Type'} : term14 _99816 A.
Proof. exact (EQ_MP (@lem3845881 _99816 A) (@lem3848232 _99816 A)). Qed.
Lemma lem3848235 {_99816 A : Type'} : term14 _99816 A.
Proof. exact (@lem3845426 _99816 A (@lem3848233 _99816 A)). Qed.
Lemma lem3848236 {_99816 A : Type'} (h1 : term10 _99816) : term31 _99816 A.
Proof. exact (@lem3848235 _99816 A (@lem3845398 _99816 h1)). Qed.
Lemma lem3848237 {_99816 A : Type'} (h1 : term10 _99816) : term29 _99816 A.
Proof. exact (@lem3848236 _99816 A h1 (@lem3845408 _99816)). Qed.
Lemma lem3848238 {_99816 A : Type'} (h1 : term10 _99816) : term26 _99816 A.
Proof. exact (@lem3848237 _99816 A h1 (@lem3845407 A)). Qed.
Lemma lem3848239 {_99816 A : Type'} (h1 : term10 _99816) : term24 _99816 A.
Proof. exact (@lem3848238 _99816 A h1 (@lem3845405 _99816)). Qed.
Lemma lem3848240 {_99816 A : Type'} (h1 : term10 _99816) : term21 _99816 A.
Proof. exact (@lem3848239 _99816 A h1 (@lem3845406 A)). Qed.
Lemma lem3848241 {_99816 A : Type'} (h1 : term10 _99816) : term18 A.
Proof. exact (@lem3848240 _99816 A h1 (@lem3845399 _99816)). Qed.
Lemma lem3848242 {_99816 : Type'} (h1 : term10 _99816) : False.
Proof. exact (@lem3848241 _99816 Prop h1 (@lem3843862 Prop)). Qed.
Lemma lem3848243 {_99816 : Type'} (h1 : term10 _99816) : (term10 _99816) = False.
Proof. exact (prop_ext (fun h2 : term10 _99816 => @lem3848242 _99816 h1) (fun h2 : False => @lem3845398 _99816 h1)). Qed.
Lemma lem3848244 {_99816 : Type'} (h1 : term10 _99816) : False.
Proof. exact (EQ_MP (@lem3848243 _99816 h1) (@lem3845398 _99816 h1)). Qed.
Lemma lem3848245 {_99816 : Type'} : term9 _99816.
Proof. exact (fun h0 : term10 _99816 => @lem3848244 _99816 h0). Qed.
Lemma lem3848246 {_99816 : Type'} : term8 _99816.
Proof. exact (EQ_MP (@lem3845397 _99816) (@lem3848245 _99816)). Qed.
