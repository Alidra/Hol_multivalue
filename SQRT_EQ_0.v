Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_EQ_0_term_abbrevs.
Require Import REAL_SGN_EQ_spec.
Require Import REAL_SGN_SQRT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1947568 (x : real) : term0 x.
Proof. exact (@lem1921867 x). Qed.
Lemma lem1947569 (x : real) : (term0 x) = ((term1 x) = (real_sgn x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1947573 (x : real) (h1 : ((real_sgn x) = term2) = (x = term2)) : ((real_sgn x) = term2) = (x = term2).
Proof. exact (h1). Qed.
Lemma lem1947574 (x : real) (h1 : ((real_sgn x) = term2) = (x = term2)) : (x = term2) = ((real_sgn x) = term2).
Proof. exact (SYM (@lem1947573 x h1)). Qed.
Lemma lem1947575 (x : real) (h1 : (x = term2) = ((real_sgn x) = term2)) : (x = term2) = ((real_sgn x) = term2).
Proof. exact (h1). Qed.
Lemma lem1947576 (x : real) (h1 : (x = term2) = ((real_sgn x) = term2)) : ((real_sgn x) = term2) = (x = term2).
Proof. exact (SYM (@lem1947575 x h1)). Qed.
Lemma lem1947577 (x : real) : (((real_sgn x) = term2) = (x = term2)) = ((x = term2) = ((real_sgn x) = term2)).
Proof. exact (prop_ext (fun h1 : ((real_sgn x) = term2) = (x = term2) => @lem1947574 x h1) (fun h1 : (x = term2) = ((real_sgn x) = term2) => @lem1947576 x h1)). Qed.
Lemma lem1947578 : term3 = term4.
Proof. exact (fun_ext (fun x : real => @lem1947577 x)). Qed.
Lemma lem1947579 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947580 : term5 = term6.
Proof. exact (MK_COMB (@lem1947579) (@lem1947578)). Qed.
Lemma lem1947581 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947582 : term7 = term8.
Proof. exact (MK_COMB (@lem1947581) (@lem1947580)). Qed.
Lemma lem1947585 (x : real) (h1 : ((real_sgn x) = term9) = (term10 x)) : ((real_sgn x) = term9) = (term10 x).
Proof. exact (h1). Qed.
Lemma lem1947586 (x : real) (h1 : ((real_sgn x) = term9) = (term10 x)) : (term10 x) = ((real_sgn x) = term9).
Proof. exact (SYM (@lem1947585 x h1)). Qed.
Lemma lem1947587 (x : real) (h1 : (term10 x) = ((real_sgn x) = term9)) : (term10 x) = ((real_sgn x) = term9).
Proof. exact (h1). Qed.
Lemma lem1947588 (x : real) (h1 : (term10 x) = ((real_sgn x) = term9)) : ((real_sgn x) = term9) = (term10 x).
Proof. exact (SYM (@lem1947587 x h1)). Qed.
Lemma lem1947589 (x : real) : (((real_sgn x) = term9) = (term10 x)) = ((term10 x) = ((real_sgn x) = term9)).
Proof. exact (prop_ext (fun h1 : ((real_sgn x) = term9) = (term10 x) => @lem1947586 x h1) (fun h1 : (term10 x) = ((real_sgn x) = term9) => @lem1947588 x h1)). Qed.
Lemma lem1947590 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1947589 x)). Qed.
Lemma lem1947591 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947592 : term13 = term14.
Proof. exact (MK_COMB (@lem1947591) (@lem1947590)). Qed.
Lemma lem1947593 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1947594 : term15 = term16.
Proof. exact (MK_COMB (@lem1947593) (@lem1947592)). Qed.
Lemma lem1947596 (x : real) (h1 : ((real_sgn x) = term17) = (term18 x)) : ((real_sgn x) = term17) = (term18 x).
Proof. exact (h1). Qed.
Lemma lem1947597 (x : real) (h1 : ((real_sgn x) = term17) = (term18 x)) : (term18 x) = ((real_sgn x) = term17).
Proof. exact (SYM (@lem1947596 x h1)). Qed.
Lemma lem1947598 (x : real) (h1 : (term18 x) = ((real_sgn x) = term17)) : (term18 x) = ((real_sgn x) = term17).
Proof. exact (h1). Qed.
Lemma lem1947599 (x : real) (h1 : (term18 x) = ((real_sgn x) = term17)) : ((real_sgn x) = term17) = (term18 x).
Proof. exact (SYM (@lem1947598 x h1)). Qed.
Lemma lem1947600 (x : real) : (((real_sgn x) = term17) = (term18 x)) = ((term18 x) = ((real_sgn x) = term17)).
Proof. exact (prop_ext (fun h1 : ((real_sgn x) = term17) = (term18 x) => @lem1947597 x h1) (fun h1 : (term18 x) = ((real_sgn x) = term17) => @lem1947599 x h1)). Qed.
Lemma lem1947601 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1947600 x)). Qed.
Lemma lem1947602 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947603 : term21 = term22.
Proof. exact (MK_COMB (@lem1947602) (@lem1947601)). Qed.
Lemma lem1947604 : term23 = term24.
Proof. exact (MK_COMB (@lem1947594) (@lem1947603)). Qed.
Lemma lem1947605 : term25 = term26.
Proof. exact (MK_COMB (@lem1947582) (@lem1947604)). Qed.
Lemma lem1947606 : term26.
Proof. exact (EQ_MP (@lem1947605) (@lem1740125)). Qed.
Lemma lem1947616 : term6.
Proof. exact (proj1 (@lem1947606)). Qed.
Lemma lem1947617 (x : real) : term27 x.
Proof. exact (@lem1947616 x). Qed.
Lemma lem1947618 (x : real) : (term27 x) = ((x = term2) = ((real_sgn x) = term2)).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1947627 (x : real) : (x = term2) = ((real_sgn x) = term2).
Proof. exact (EQ_MP (@lem1947618 x) (@lem1947617 x)). Qed.
Lemma lem1947628 (x : real) : ((sqrt x) = term2) = ((term1 x) = term2).
Proof. exact (@lem1947627 (sqrt x)). Qed.
Lemma lem1947629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1947630 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1947629) (@lem1947628 x)). Qed.
Lemma lem1947632 (x : real) : (x = term2) = ((real_sgn x) = term2).
Proof. exact (EQ_MP (@lem1947618 x) (@lem1947617 x)). Qed.
Lemma lem1947633 (x : real) : (((sqrt x) = term2) = (x = term2)) = (((term1 x) = term2) = ((real_sgn x) = term2)).
Proof. exact (MK_COMB (@lem1947630 x) (@lem1947632 x)). Qed.
Lemma lem1947634 : term30 = term31.
Proof. exact (fun_ext (fun x : real => @lem1947633 x)). Qed.
Lemma lem1947635 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947636 : term32 = term33.
Proof. exact (MK_COMB (@lem1947635) (@lem1947634)). Qed.
Lemma lem1947637 : term33 = term32.
Proof. exact (SYM (@lem1947636)). Qed.
Lemma lem1947647 (x : real) : (term1 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem1947569 x) (@lem1947568 x)). Qed.
Lemma lem1947648 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1947649 (x : real) : (term34 x) = (term35 x).
Proof. exact (MK_COMB (@lem1947648) (@lem1947647 x)). Qed.
Lemma lem1947650 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1947651 (x : real) : ((term1 x) = term2) = ((real_sgn x) = term2).
Proof. exact (MK_COMB (@lem1947649 x) (@lem1947650)). Qed.
Lemma lem1947654 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1947655 (x : real) : (term29 x) = (term36 x).
Proof. exact (MK_COMB (@lem1947654) (@lem1947651 x)). Qed.
Lemma lem1947658 (x : real) : ((real_sgn x) = term2) = ((real_sgn x) = term2).
Proof. exact (eq_refl ((real_sgn x) = term2)). Qed.
Lemma lem1947659 (x : real) : (((term1 x) = term2) = ((real_sgn x) = term2)) = (((real_sgn x) = term2) = ((real_sgn x) = term2)).
Proof. exact (MK_COMB (@lem1947655 x) (@lem1947658 x)). Qed.
Lemma lem1947661 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1947662 (x : Prop) : (x = x) = True.
Proof. exact (@lem1947661 Prop x). Qed.
Lemma lem1947663 (x : real) : (((real_sgn x) = term2) = ((real_sgn x) = term2)) = True.
Proof. exact (@lem1947662 ((real_sgn x) = term2)). Qed.
Lemma lem1947664 (x : real) : (((term1 x) = term2) = ((real_sgn x) = term2)) = True.
Proof. exact (TRANS (@lem1947659 x) (@lem1947663 x)). Qed.
Lemma lem1947665 : term31 = term37.
Proof. exact (fun_ext (fun x : real => @lem1947664 x)). Qed.
Lemma lem1947666 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1947667 : term33 = term38.
Proof. exact (MK_COMB (@lem1947666) (@lem1947665)). Qed.
Lemma lem1947669 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1947670 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1947669 real t). Qed.
Lemma lem1947671 : term38 = True.
Proof. exact (@lem1947670 True). Qed.
Lemma lem1947672 : term33 = True.
Proof. exact (TRANS (@lem1947667) (@lem1947671)). Qed.
Lemma lem1947673 : True = term33.
Proof. exact (SYM (@lem1947672)). Qed.
Lemma lem1947674 : term33.
Proof. exact (EQ_MP (@lem1947673) (@lem0)). Qed.
Lemma lem1947675 : term32.
Proof. exact (EQ_MP (@lem1947637) (@lem1947674)). Qed.
