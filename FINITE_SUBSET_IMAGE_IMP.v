Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_SUBSET_IMAGE_IMP_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import FINITE_SUBSET_IMAGE_spec.
Require Import SUBSET_REFL_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem3698380 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem3698381 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem3698382 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem3698381 t1) (@lem3698380 t1)). Qed.
Lemma lem3698383 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem3698382 t1 t2). Qed.
Lemma lem3698384 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem3698385 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem3698384 t1 t2) (@lem3698383 t1 t2)). Qed.
Lemma lem3698386 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem3698385 t1 t2 t3). Qed.
Lemma lem3698387 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem3698388 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem3698387 t1 t2 t3) (@lem3698386 t1 t2 t3)). Qed.
Lemma lem3698389 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem3698388 t1 t2 t3)). Qed.
Lemma lem3698391 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3698392 {A B : Type'} : (term8 A B) = (term9 A B).
Proof. exact (@lem3698391 (term8 A B)). Qed.
Lemma lem3698393 {A B : Type'} : (term9 A B) = (term8 A B).
Proof. exact (SYM (@lem3698392 A B)). Qed.
Lemma lem3698394 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem3698395 {B : Type'} : term11 B.
Proof. exact (@lem3217397 B). Qed.
Lemma lem3698396 {A : Type'} : term11 A.
Proof. exact (@lem3217397 A). Qed.
Lemma lem3698397 {A B : Type'} : term12 A B.
Proof. exact (@lem3698379 A B). Qed.
Lemma lem3698398 {A : Type'} : term13 A.
Proof. exact (@lem3698379 A A). Qed.
Lemma lem3698402 {B : Type'} : term13 B.
Proof. exact (@lem3698379 B B). Qed.
Lemma lem3698408 {A B : Type'} (h1 : term14 A B) : term14 A B.
Proof. exact (h1). Qed.
Lemma lem3698409 {A B : Type'} : term15 A B.
Proof. exact (fun h0 : term14 A B => @lem3698408 A B h0). Qed.
Lemma lem3698410 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem3698411 {A B : Type'} (h1 : term14 A B) : term14 A B.
Proof. exact (h1). Qed.
Lemma lem3698412 {A B : Type'} (h1 : term14 A B) (h2 : term15 A B) : term14 A B.
Proof. exact (@lem3698410 A B h2 (@lem3698411 A B h1)). Qed.
Lemma lem3698413 {A B : Type'} (h1 : term14 A B) : term16 A B.
Proof. exact (fun h0 : term15 A B => @lem3698412 A B h1 h0). Qed.
Lemma lem3698414 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (h1). Qed.
Lemma lem3698415 {A B : Type'} (h1 : term14 A B) (h2 : term15 A B) : term14 A B.
Proof. exact (@lem3698413 A B h1 (@lem3698414 A B h2)). Qed.
Lemma lem3698416 {A B : Type'} (h1 : term15 A B) : term15 A B.
Proof. exact (fun h0 : term14 A B => @lem3698415 A B h0 h1). Qed.
Lemma lem3698417 {A B : Type'} : term17 A B.
Proof. exact (fun h0 : term15 A B => @lem3698416 A B h0). Qed.
Lemma lem3698420 {A B : Type'} : term15 A B.
Proof. exact (@lem3698417 A B (@lem3698409 A B)). Qed.
Lemma lem3698421 {A B : Type'} : term15 A B.
Proof. exact (@lem3698420 A B). Qed.
Lemma lem3698623 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3698624 {B : Type'} : (term18 B) = (term19 B).
Proof. exact (@lem3698623 (term11 B)). Qed.
Lemma lem3698629 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (eq_refl (term20 A)). Qed.
Lemma lem3698630 {A B : Type'} : (term21 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem3698629 A) (@lem3698624 B)). Qed.
Lemma lem3698633 {B : Type'} : (term23 B) = (term23 B).
Proof. exact (eq_refl (term23 B)). Qed.
Lemma lem3698634 {A B : Type'} : (term24 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem3698633 B) (@lem3698630 A B)). Qed.
Lemma lem3698637 {A B : Type'} : (term26 A B) = (term26 A B).
Proof. exact (eq_refl (term26 A B)). Qed.
Lemma lem3698638 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (MK_COMB (@lem3698637 A B) (@lem3698634 A B)). Qed.
Lemma lem3698641 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (eq_refl (term23 A)). Qed.
Lemma lem3698642 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3698641 A) (@lem3698638 A B)). Qed.
Lemma lem3698645 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (eq_refl (term31 A B)). Qed.
Lemma lem3698652 {A B : Type'} : (term14 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem3698645 A B) (@lem3698642 A B)). Qed.
Lemma lem3698653 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3698654 {B : Type'} : (term33 B) = (term33 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3698653 B s)). Qed.
Lemma lem3698655 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3698656 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (MK_COMB (@lem3698655 B) (@lem3698654 B)). Qed.
Lemma lem3698657 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3698658 {B : Type'} : (term19 B) = (term19 B).
Proof. exact (MK_COMB (@lem3698657) (@lem3698656 B)). Qed.
Lemma lem3698659 {A : Type'} (s : A -> Prop) : (@SUBSET A s s) = (@SUBSET A s s).
Proof. exact (eq_refl (@SUBSET A s s)). Qed.
Lemma lem3698660 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3698659 A s)). Qed.
Lemma lem3698661 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698662 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3698661 A) (@lem3698660 A)). Qed.
Lemma lem3698663 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3698664 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem3698663) (@lem3698662 A)). Qed.
Lemma lem3698665 {A B : Type'} : (term22 A B) = (term22 A B).
Proof. exact (MK_COMB (@lem3698664 A) (@lem3698658 B)). Qed.
Lemma lem3698674 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term34 B s t f s') = (term34 B s t f s').
Proof. exact (eq_refl (term34 B s t f s')). Qed.
Lemma lem3698675 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term35 B s t f) = (term35 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3698674 B s t f s')). Qed.
Lemma lem3698676 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3698677 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term36 B s t f) = (term36 B s t f).
Proof. exact (MK_COMB (@lem3698676 B) (@lem3698675 B s t f)). Qed.
Lemma lem3698684 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term37 B t f s) = (term37 B t f s).
Proof. exact (eq_refl (term37 B t f s)). Qed.
Lemma lem3698685 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term38 B t f s) = (term36 B s t f)) = ((term38 B t f s) = (term36 B s t f)).
Proof. exact (MK_COMB (@lem3698684 B t f s) (@lem3698677 B s t f)). Qed.
Lemma lem3698686 {B : Type'} (s : B -> Prop) (f : B -> B) : (term39 B s f) = (term39 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3698685 B s t f)). Qed.
Lemma lem3698687 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3698688 {B : Type'} (s : B -> Prop) (f : B -> B) : (term40 B s f) = (term40 B s f).
Proof. exact (MK_COMB (@lem3698687 B) (@lem3698686 B s f)). Qed.
Lemma lem3698689 {B : Type'} (f : B -> B) : (term41 B f) = (term41 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3698688 B s f)). Qed.
Lemma lem3698690 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3698691 {B : Type'} (f : B -> B) : (term42 B f) = (term42 B f).
Proof. exact (MK_COMB (@lem3698690 B) (@lem3698689 B f)). Qed.
Lemma lem3698692 {B : Type'} : (term43 B) = (term43 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3698691 B f)). Qed.
Lemma lem3698693 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3698694 {B : Type'} : (term13 B) = (term13 B).
Proof. exact (MK_COMB (@lem3698693 B) (@lem3698692 B)). Qed.
Lemma lem3698695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3698696 {B : Type'} : (term23 B) = (term23 B).
Proof. exact (MK_COMB (@lem3698695) (@lem3698694 B)). Qed.
Lemma lem3698697 {A B : Type'} : (term25 A B) = (term25 A B).
Proof. exact (MK_COMB (@lem3698696 B) (@lem3698665 A B)). Qed.
Lemma lem3698706 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term44 A B s t f s') = (term44 A B s t f s').
Proof. exact (eq_refl (term44 A B s t f s')). Qed.
Lemma lem3698707 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term45 A B s t f) = (term45 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698706 A B s t f s')). Qed.
Lemma lem3698708 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3698709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term46 A B s t f) = (term46 A B s t f).
Proof. exact (MK_COMB (@lem3698708 A) (@lem3698707 A B s t f)). Qed.
Lemma lem3698716 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term47 A B t f s) = (term47 A B t f s).
Proof. exact (eq_refl (term47 A B t f s)). Qed.
Lemma lem3698717 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term48 A B t f s) = (term46 A B s t f)) = ((term48 A B t f s) = (term46 A B s t f)).
Proof. exact (MK_COMB (@lem3698716 A B t f s) (@lem3698709 A B s t f)). Qed.
Lemma lem3698718 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term49 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3698717 A B s t f)). Qed.
Lemma lem3698719 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3698720 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B s f) = (term50 A B s f).
Proof. exact (MK_COMB (@lem3698719 B) (@lem3698718 A B s f)). Qed.
Lemma lem3698721 {A B : Type'} (f : A -> B) : (term51 A B f) = (term51 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3698720 A B s f)). Qed.
Lemma lem3698722 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698723 {A B : Type'} (f : A -> B) : (term52 A B f) = (term52 A B f).
Proof. exact (MK_COMB (@lem3698722 A) (@lem3698721 A B f)). Qed.
Lemma lem3698724 {A B : Type'} : (term53 A B) = (term53 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3698723 A B f)). Qed.
Lemma lem3698725 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3698726 {A B : Type'} : (term12 A B) = (term12 A B).
Proof. exact (MK_COMB (@lem3698725 A B) (@lem3698724 A B)). Qed.
Lemma lem3698727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3698728 {A B : Type'} : (term26 A B) = (term26 A B).
Proof. exact (MK_COMB (@lem3698727) (@lem3698726 A B)). Qed.
Lemma lem3698729 {A B : Type'} : (term28 A B) = (term28 A B).
Proof. exact (MK_COMB (@lem3698728 A B) (@lem3698697 A B)). Qed.
Lemma lem3698738 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term34 A s t f s') = (term34 A s t f s').
Proof. exact (eq_refl (term34 A s t f s')). Qed.
Lemma lem3698739 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term35 A s t f) = (term35 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698738 A s t f s')). Qed.
Lemma lem3698740 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3698741 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term36 A s t f) = (term36 A s t f).
Proof. exact (MK_COMB (@lem3698740 A) (@lem3698739 A s t f)). Qed.
Lemma lem3698748 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term37 A t f s) = (term37 A t f s).
Proof. exact (eq_refl (term37 A t f s)). Qed.
Lemma lem3698749 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term38 A t f s) = (term36 A s t f)) = ((term38 A t f s) = (term36 A s t f)).
Proof. exact (MK_COMB (@lem3698748 A t f s) (@lem3698741 A s t f)). Qed.
Lemma lem3698750 {A : Type'} (s : A -> Prop) (f : A -> A) : (term39 A s f) = (term39 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3698749 A s t f)). Qed.
Lemma lem3698751 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698752 {A : Type'} (s : A -> Prop) (f : A -> A) : (term40 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem3698751 A) (@lem3698750 A s f)). Qed.
Lemma lem3698753 {A : Type'} (f : A -> A) : (term41 A f) = (term41 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3698752 A s f)). Qed.
Lemma lem3698754 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698755 {A : Type'} (f : A -> A) : (term42 A f) = (term42 A f).
Proof. exact (MK_COMB (@lem3698754 A) (@lem3698753 A f)). Qed.
Lemma lem3698756 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3698755 A f)). Qed.
Lemma lem3698757 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3698758 {A : Type'} : (term13 A) = (term13 A).
Proof. exact (MK_COMB (@lem3698757 A) (@lem3698756 A)). Qed.
Lemma lem3698759 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3698760 {A : Type'} : (term23 A) = (term23 A).
Proof. exact (MK_COMB (@lem3698759) (@lem3698758 A)). Qed.
Lemma lem3698761 {A B : Type'} : (term30 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem3698760 A) (@lem3698729 A B)). Qed.
Lemma lem3698770 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term54 A B s t f s') = (term54 A B s t f s').
Proof. exact (eq_refl (term54 A B s t f s')). Qed.
Lemma lem3698771 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term55 A B s t f) = (term55 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698770 A B s t f s')). Qed.
Lemma lem3698772 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3698773 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term56 A B s t f) = (term56 A B s t f).
Proof. exact (MK_COMB (@lem3698772 A) (@lem3698771 A B s t f)). Qed.
Lemma lem3698780 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term57 A B t f s) = (term57 A B t f s).
Proof. exact (eq_refl (term57 A B t f s)). Qed.
Lemma lem3698781 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term58 A B s t f) = (term58 A B s t f).
Proof. exact (MK_COMB (@lem3698780 A B t f s) (@lem3698773 A B s t f)). Qed.
Lemma lem3698782 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term59 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3698781 A B s t f)). Qed.
Lemma lem3698783 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3698784 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term60 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem3698783 B) (@lem3698782 A B s f)). Qed.
Lemma lem3698785 {A B : Type'} (f : A -> B) : (term61 A B f) = (term61 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3698784 A B s f)). Qed.
Lemma lem3698786 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698787 {A B : Type'} (f : A -> B) : (term62 A B f) = (term62 A B f).
Proof. exact (MK_COMB (@lem3698786 A) (@lem3698785 A B f)). Qed.
Lemma lem3698788 {A B : Type'} : (term63 A B) = (term63 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3698787 A B f)). Qed.
Lemma lem3698789 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3698790 {A B : Type'} : (term8 A B) = (term8 A B).
Proof. exact (MK_COMB (@lem3698789 A B) (@lem3698788 A B)). Qed.
Lemma lem3698791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3698792 {A B : Type'} : (term10 A B) = (term10 A B).
Proof. exact (MK_COMB (@lem3698791) (@lem3698790 A B)). Qed.
Lemma lem3698793 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3698794 {A B : Type'} : (term31 A B) = (term31 A B).
Proof. exact (MK_COMB (@lem3698793) (@lem3698792 A B)). Qed.
Lemma lem3698795 {A B : Type'} : (term32 A B) = (term32 A B).
Proof. exact (MK_COMB (@lem3698794 A B) (@lem3698761 A B)). Qed.
Lemma lem3698942 {A B : Type'} : (term14 A B) = (term32 A B).
Proof. exact (TRANS (@lem3698652 A B) (@lem3698795 A B)). Qed.
Lemma lem3698943 {A B : Type'} : (term32 A B) = (term14 A B).
Proof. exact (SYM (@lem3698942 A B)). Qed.
Lemma lem3698944 {A B : Type'} (h1 : term10 A B) : term10 A B.
Proof. exact (h1). Qed.
Lemma lem3698945 {A : Type'} (h1 : term13 A) : term13 A.
Proof. exact (h1). Qed.
Lemma lem3698946 {A B : Type'} (h1 : term12 A B) : term12 A B.
Proof. exact (h1). Qed.
Lemma lem3698947 {B : Type'} (h1 : term13 B) : term13 B.
Proof. exact (h1). Qed.
Lemma lem3698949 {B : Type'} (h1 : term11 B) : term11 B.
Proof. exact (h1). Qed.
Lemma lem3698962 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term64 A B s t f s') = (term65 A B s t f s').
Proof. exact (@lem17045 (@SUBSET A s' s) (term66 A B t f s')). Qed.
Lemma lem3698964 {A : Type'} (s' : A -> Prop) : (term67 A s') = (term67 A s').
Proof. exact (eq_refl (term67 A s')). Qed.
Lemma lem3698965 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term68 A B s t f s') = (term69 A B s t f s').
Proof. exact (MK_COMB (@lem3698964 A s') (@lem3698962 A B s t f s')). Qed.
Lemma lem3698966 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term70 A B s t f s') = (term68 A B s t f s').
Proof. exact (@lem17045 (@FINITE A s') (term71 A B s t f s')). Qed.
Lemma lem3698967 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term70 A B s t f s') = (term69 A B s t f s').
Proof. exact (TRANS (@lem3698966 A B s t f s') (@lem3698965 A B s t f s')). Qed.
Lemma lem3698968 {A : Type'} (P : type686 A) : (term72 A P) = (term73 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3698969 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term74 A B s t f) = (term75 A B s t f).
Proof. exact (@lem3698968 A (term55 A B s t f)). Qed.
Lemma lem3698970 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term76 A B s t f s') = (term54 A B s t f s').
Proof. exact (eq_refl (term76 A B s t f s')). Qed.
Lemma lem3698971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3698972 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term77 A B s t f s') = (term70 A B s t f s').
Proof. exact (MK_COMB (@lem3698971) (@lem3698970 A B s t f s')). Qed.
Lemma lem3698973 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term77 A B s t f s') = (term69 A B s t f s').
Proof. exact (TRANS (@lem3698972 A B s t f s') (@lem3698967 A B s t f s')). Qed.
Lemma lem3698974 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term78 A B s t f) = (term79 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3698973 A B s t f s')). Qed.
Lemma lem3698975 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3698976 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term75 A B s t f) = (term80 A B s t f).
Proof. exact (MK_COMB (@lem3698975 A) (@lem3698974 A B s t f)). Qed.
Lemma lem3698977 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term74 A B s t f) = (term80 A B s t f).
Proof. exact (TRANS (@lem3698969 A B s t f) (@lem3698976 A B s t f)). Qed.
Lemma lem3698979 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B t f s) = (term81 A B t f s).
Proof. exact (eq_refl (term81 A B t f s)). Qed.
Lemma lem3698980 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term82 A B s t f) = (term83 A B s t f).
Proof. exact (MK_COMB (@lem3698979 A B t f s) (@lem3698977 A B s t f)). Qed.
Lemma lem3698981 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term84 A B s t f) = (term82 A B s t f).
Proof. exact (@lem17362 (term48 A B t f s) (term56 A B s t f)). Qed.
Lemma lem3698982 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term84 A B s t f) = (term83 A B s t f).
Proof. exact (TRANS (@lem3698981 A B s t f) (@lem3698980 A B s t f)). Qed.
Lemma lem3698983 {B : Type'} (P : type686 B) : (term85 B P) = (term86 B P).
Proof. exact (@lem18392 (B -> Prop) P). Qed.
Lemma lem3698984 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term87 A B s f) = (term88 A B s f).
Proof. exact (@lem3698983 B (term59 A B s f)). Qed.
Lemma lem3698985 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term89 A B s f t) = (term58 A B s t f).
Proof. exact (eq_refl (term89 A B s f t)). Qed.
Lemma lem3698986 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3698987 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term90 A B s f t) = (term84 A B s t f).
Proof. exact (MK_COMB (@lem3698986) (@lem3698985 A B s t f)). Qed.
Lemma lem3698988 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term90 A B s f t) = (term83 A B s t f).
Proof. exact (TRANS (@lem3698987 A B s t f) (@lem3698982 A B s t f)). Qed.
Lemma lem3698989 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term91 A B s f) = (term92 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3698988 A B s t f)). Qed.
Lemma lem3698990 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3698991 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term88 A B s f) = (term93 A B s f).
Proof. exact (MK_COMB (@lem3698990 B) (@lem3698989 A B s f)). Qed.
Lemma lem3698992 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term87 A B s f) = (term93 A B s f).
Proof. exact (TRANS (@lem3698984 A B s f) (@lem3698991 A B s f)). Qed.
Lemma lem3698993 {A : Type'} (P : type686 A) : (term85 A P) = (term86 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3698994 {A B : Type'} (f : A -> B) : (term94 A B f) = (term95 A B f).
Proof. exact (@lem3698993 A (term61 A B f)). Qed.
Lemma lem3698995 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term96 A B f s) = (term60 A B s f).
Proof. exact (eq_refl (term96 A B f s)). Qed.
Lemma lem3698996 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3698997 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term97 A B f s) = (term87 A B s f).
Proof. exact (MK_COMB (@lem3698996) (@lem3698995 A B s f)). Qed.
Lemma lem3698998 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term97 A B f s) = (term93 A B s f).
Proof. exact (TRANS (@lem3698997 A B s f) (@lem3698992 A B s f)). Qed.
Lemma lem3698999 {A B : Type'} (f : A -> B) : (term98 A B f) = (term99 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3698998 A B s f)). Qed.
Lemma lem3699000 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3699001 {A B : Type'} (f : A -> B) : (term95 A B f) = (term100 A B f).
Proof. exact (MK_COMB (@lem3699000 A) (@lem3698999 A B f)). Qed.
Lemma lem3699002 {A B : Type'} (f : A -> B) : (term94 A B f) = (term100 A B f).
Proof. exact (TRANS (@lem3698994 A B f) (@lem3699001 A B f)). Qed.
Lemma lem3699003 {A B : Type'} (P : type572 A B) : (term101 A B P) = (term102 A B P).
Proof. exact (@lem18392 (A -> B) P). Qed.
Lemma lem3699004 {A B : Type'} : (term10 A B) = (term103 A B).
Proof. exact (@lem3699003 A B (term63 A B)). Qed.
Lemma lem3699005 {A B : Type'} (f : A -> B) : (term104 A B f) = (term62 A B f).
Proof. exact (eq_refl (term104 A B f)). Qed.
Lemma lem3699006 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3699007 {A B : Type'} (f : A -> B) : (term105 A B f) = (term94 A B f).
Proof. exact (MK_COMB (@lem3699006) (@lem3699005 A B f)). Qed.
Lemma lem3699008 {A B : Type'} (f : A -> B) : (term105 A B f) = (term100 A B f).
Proof. exact (TRANS (@lem3699007 A B f) (@lem3699002 A B f)). Qed.
Lemma lem3699009 {A B : Type'} : (term106 A B) = (term107 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3699008 A B f)). Qed.
Lemma lem3699010 {A B : Type'} : (@ex (A -> B)) = (@ex (A -> B)).
Proof. exact (eq_refl (@ex (A -> B))). Qed.
Lemma lem3699011 {A B : Type'} : (term103 A B) = (term108 A B).
Proof. exact (MK_COMB (@lem3699010 A B) (@lem3699009 A B)). Qed.
Lemma lem3699120 {A B : Type'} : (term10 A B) = (term108 A B).
Proof. exact (TRANS (@lem3699004 A B) (@lem3699011 A B)). Qed.
Lemma lem3699121 {A B : Type'} (h1 : term10 A B) : term108 A B.
Proof. exact (EQ_MP (@lem3699120 A B) (@lem3698944 A B h1)). Qed.
Lemma lem3699130 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term109 A t f s) = (term110 A t f s).
Proof. exact (@lem17045 (@FINITE A t) (term111 A t f s)). Qed.
Lemma lem3699144 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term112 A s t f s') = (term113 A s t f s').
Proof. exact (@lem17045 (@SUBSET A s' s) (t = (@IMAGE A A f s'))). Qed.
Lemma lem3699149 {A : Type'} (s' : A -> Prop) : (term67 A s') = (term67 A s').
Proof. exact (eq_refl (term67 A s')). Qed.
Lemma lem3699150 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term114 A s t f s') = (term115 A s t f s').
Proof. exact (MK_COMB (@lem3699149 A s') (@lem3699144 A s t f s')). Qed.
Lemma lem3699151 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term116 A s t f s') = (term114 A s t f s').
Proof. exact (@lem17045 (@FINITE A s') (term117 A s t f s')). Qed.
Lemma lem3699152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term116 A s t f s') = (term115 A s t f s').
Proof. exact (TRANS (@lem3699151 A s t f s') (@lem3699150 A s t f s')). Qed.
Lemma lem3699155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term34 A s t f s') = (term34 A s t f s').
Proof. exact (eq_refl (term34 A s t f s')). Qed.
Lemma lem3699156 {A : Type'} (P : type686 A) : (term72 A P) = (term73 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3699157 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term118 A s t f) = (term119 A s t f).
Proof. exact (@lem3699156 A (term35 A s t f)). Qed.
Lemma lem3699158 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term120 A s t f s') = (term34 A s t f s').
Proof. exact (eq_refl (term120 A s t f s')). Qed.
Lemma lem3699159 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3699160 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term121 A s t f s') = (term116 A s t f s').
Proof. exact (MK_COMB (@lem3699159) (@lem3699158 A s t f s')). Qed.
Lemma lem3699161 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term121 A s t f s') = (term115 A s t f s').
Proof. exact (TRANS (@lem3699160 A s t f s') (@lem3699152 A s t f s')). Qed.
Lemma lem3699162 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term122 A s t f) = (term123 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3699161 A s t f s')). Qed.
Lemma lem3699163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699164 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term119 A s t f) = (term124 A s t f).
Proof. exact (MK_COMB (@lem3699163 A) (@lem3699162 A s t f)). Qed.
Lemma lem3699165 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term118 A s t f) = (term124 A s t f).
Proof. exact (TRANS (@lem3699157 A s t f) (@lem3699164 A s t f)). Qed.
Lemma lem3699166 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term35 A s t f) = (term35 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3699155 A s t f s')). Qed.
Lemma lem3699167 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3699168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term36 A s t f) = (term36 A s t f).
Proof. exact (MK_COMB (@lem3699167 A) (@lem3699166 A s t f)). Qed.
Lemma lem3699169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3699170 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term125 A t f s) = (term126 A t f s).
Proof. exact (MK_COMB (@lem3699169) (@lem3699130 A t f s)). Qed.
Lemma lem3699171 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term127 A s t f) = (term128 A s t f).
Proof. exact (MK_COMB (@lem3699170 A t f s) (@lem3699168 A s t f)). Qed.
Lemma lem3699173 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term129 A t f s) = (term129 A t f s).
Proof. exact (eq_refl (term129 A t f s)). Qed.
Lemma lem3699174 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term130 A s t f) = (term131 A s t f).
Proof. exact (MK_COMB (@lem3699173 A t f s) (@lem3699165 A s t f)). Qed.
Lemma lem3699175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699176 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term132 A s t f) = (term133 A s t f).
Proof. exact (MK_COMB (@lem3699175) (@lem3699174 A s t f)). Qed.
Lemma lem3699177 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term134 A s t f) = (term135 A s t f).
Proof. exact (MK_COMB (@lem3699176 A s t f) (@lem3699171 A s t f)). Qed.
Lemma lem3699178 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term38 A t f s) = (term36 A s t f)) = (term134 A s t f).
Proof. exact (@lem17784 (term38 A t f s) (term36 A s t f)). Qed.
Lemma lem3699179 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term38 A t f s) = (term36 A s t f)) = (term135 A s t f).
Proof. exact (TRANS (@lem3699178 A s t f) (@lem3699177 A s t f)). Qed.
Lemma lem3699180 {A : Type'} (s : A -> Prop) (f : A -> A) : (term39 A s f) = (term136 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699179 A s t f)). Qed.
Lemma lem3699181 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699182 {A : Type'} (s : A -> Prop) (f : A -> A) : (term40 A s f) = (term137 A s f).
Proof. exact (MK_COMB (@lem3699181 A) (@lem3699180 A s f)). Qed.
Lemma lem3699183 {A : Type'} (f : A -> A) : (term41 A f) = (term138 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699182 A s f)). Qed.
Lemma lem3699184 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699185 {A : Type'} (f : A -> A) : (term42 A f) = (term139 A f).
Proof. exact (MK_COMB (@lem3699184 A) (@lem3699183 A f)). Qed.
Lemma lem3699186 {A : Type'} : (term43 A) = (term140 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699185 A f)). Qed.
Lemma lem3699187 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699188 {A : Type'} : (term13 A) = (term141 A).
Proof. exact (MK_COMB (@lem3699187 A) (@lem3699186 A)). Qed.
Lemma lem3699198 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3699199 {A : Type'} (P : type686 A) (Q : type686 A) : (term144 A P Q) = (term145 A P Q).
Proof. exact (@lem3699198 (A -> Prop) P Q). Qed.
Lemma lem3699200 {A : Type'} (s : A -> Prop) (f : A -> A) : (term146 A s f) = (term147 A s f).
Proof. exact (@lem3699199 A (term148 A s f) (term149 A s f)). Qed.
Lemma lem3699201 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term150 A s f t) = (term131 A s t f).
Proof. exact (eq_refl (term150 A s f t)). Qed.
Lemma lem3699202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699203 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term151 A s f t) = (term133 A s t f).
Proof. exact (MK_COMB (@lem3699202) (@lem3699201 A s t f)). Qed.
Lemma lem3699204 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term152 A s f t) = (term128 A s t f).
Proof. exact (eq_refl (term152 A s f t)). Qed.
Lemma lem3699205 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term153 A s f t) = (term135 A s t f).
Proof. exact (MK_COMB (@lem3699203 A s t f) (@lem3699204 A s t f)). Qed.
Lemma lem3699206 {A : Type'} (s : A -> Prop) (f : A -> A) : (term154 A s f) = (term136 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699205 A s t f)). Qed.
Lemma lem3699207 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699208 {A : Type'} (s : A -> Prop) (f : A -> A) : (term146 A s f) = (term137 A s f).
Proof. exact (MK_COMB (@lem3699207 A) (@lem3699206 A s f)). Qed.
Lemma lem3699209 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699210 {A : Type'} (s : A -> Prop) (f : A -> A) : (term155 A s f) = (term156 A s f).
Proof. exact (MK_COMB (@lem3699209) (@lem3699208 A s f)). Qed.
Lemma lem3699211 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term150 A s f t) = (term131 A s t f).
Proof. exact (eq_refl (term150 A s f t)). Qed.
Lemma lem3699212 {A : Type'} (s : A -> Prop) (f : A -> A) : (term157 A s f) = (term148 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699211 A s t f)). Qed.
Lemma lem3699213 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699214 {A : Type'} (s : A -> Prop) (f : A -> A) : (term158 A s f) = (term159 A s f).
Proof. exact (MK_COMB (@lem3699213 A) (@lem3699212 A s f)). Qed.
Lemma lem3699215 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699216 {A : Type'} (s : A -> Prop) (f : A -> A) : (term160 A s f) = (term161 A s f).
Proof. exact (MK_COMB (@lem3699215) (@lem3699214 A s f)). Qed.
Lemma lem3699217 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term152 A s f t) = (term128 A s t f).
Proof. exact (eq_refl (term152 A s f t)). Qed.
Lemma lem3699218 {A : Type'} (s : A -> Prop) (f : A -> A) : (term162 A s f) = (term149 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699217 A s t f)). Qed.
Lemma lem3699219 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699220 {A : Type'} (s : A -> Prop) (f : A -> A) : (term163 A s f) = (term164 A s f).
Proof. exact (MK_COMB (@lem3699219 A) (@lem3699218 A s f)). Qed.
Lemma lem3699221 {A : Type'} (s : A -> Prop) (f : A -> A) : (term147 A s f) = (term165 A s f).
Proof. exact (MK_COMB (@lem3699216 A s f) (@lem3699220 A s f)). Qed.
Lemma lem3699222 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term146 A s f) = (term147 A s f)) = ((term137 A s f) = (term165 A s f)).
Proof. exact (MK_COMB (@lem3699210 A s f) (@lem3699221 A s f)). Qed.
Lemma lem3699223 {A : Type'} (s : A -> Prop) (f : A -> A) : (term137 A s f) = (term165 A s f).
Proof. exact (EQ_MP (@lem3699222 A s f) (@lem3699200 A s f)). Qed.
Lemma lem3699396 {A : Type'} (f : A -> A) : (term138 A f) = (term166 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699223 A s f)). Qed.
Lemma lem3699397 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699398 {A : Type'} (f : A -> A) : (term139 A f) = (term167 A f).
Proof. exact (MK_COMB (@lem3699397 A) (@lem3699396 A f)). Qed.
Lemma lem3699400 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3699401 {A : Type'} (P : type686 A) (Q : type686 A) : (term144 A P Q) = (term145 A P Q).
Proof. exact (@lem3699400 (A -> Prop) P Q). Qed.
Lemma lem3699402 {A : Type'} (f : A -> A) : (term168 A f) = (term169 A f).
Proof. exact (@lem3699401 A (term170 A f) (term171 A f)). Qed.
Lemma lem3699403 {A : Type'} (s : A -> Prop) (f : A -> A) : (term172 A f s) = (term159 A s f).
Proof. exact (eq_refl (term172 A f s)). Qed.
Lemma lem3699404 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699405 {A : Type'} (s : A -> Prop) (f : A -> A) : (term173 A f s) = (term161 A s f).
Proof. exact (MK_COMB (@lem3699404) (@lem3699403 A s f)). Qed.
Lemma lem3699406 {A : Type'} (s : A -> Prop) (f : A -> A) : (term174 A f s) = (term164 A s f).
Proof. exact (eq_refl (term174 A f s)). Qed.
Lemma lem3699407 {A : Type'} (s : A -> Prop) (f : A -> A) : (term175 A f s) = (term165 A s f).
Proof. exact (MK_COMB (@lem3699405 A s f) (@lem3699406 A s f)). Qed.
Lemma lem3699408 {A : Type'} (f : A -> A) : (term176 A f) = (term166 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699407 A s f)). Qed.
Lemma lem3699409 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699410 {A : Type'} (f : A -> A) : (term168 A f) = (term167 A f).
Proof. exact (MK_COMB (@lem3699409 A) (@lem3699408 A f)). Qed.
Lemma lem3699411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699412 {A : Type'} (f : A -> A) : (term177 A f) = (term178 A f).
Proof. exact (MK_COMB (@lem3699411) (@lem3699410 A f)). Qed.
Lemma lem3699413 {A : Type'} (s : A -> Prop) (f : A -> A) : (term172 A f s) = (term159 A s f).
Proof. exact (eq_refl (term172 A f s)). Qed.
Lemma lem3699414 {A : Type'} (f : A -> A) : (term179 A f) = (term170 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699413 A s f)). Qed.
Lemma lem3699415 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699416 {A : Type'} (f : A -> A) : (term180 A f) = (term181 A f).
Proof. exact (MK_COMB (@lem3699415 A) (@lem3699414 A f)). Qed.
Lemma lem3699417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699418 {A : Type'} (f : A -> A) : (term182 A f) = (term183 A f).
Proof. exact (MK_COMB (@lem3699417) (@lem3699416 A f)). Qed.
Lemma lem3699419 {A : Type'} (s : A -> Prop) (f : A -> A) : (term174 A f s) = (term164 A s f).
Proof. exact (eq_refl (term174 A f s)). Qed.
Lemma lem3699420 {A : Type'} (f : A -> A) : (term184 A f) = (term171 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699419 A s f)). Qed.
Lemma lem3699421 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699422 {A : Type'} (f : A -> A) : (term185 A f) = (term186 A f).
Proof. exact (MK_COMB (@lem3699421 A) (@lem3699420 A f)). Qed.
Lemma lem3699423 {A : Type'} (f : A -> A) : (term169 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem3699418 A f) (@lem3699422 A f)). Qed.
Lemma lem3699424 {A : Type'} (f : A -> A) : ((term168 A f) = (term169 A f)) = ((term167 A f) = (term187 A f)).
Proof. exact (MK_COMB (@lem3699412 A f) (@lem3699423 A f)). Qed.
Lemma lem3699425 {A : Type'} (f : A -> A) : (term167 A f) = (term187 A f).
Proof. exact (EQ_MP (@lem3699424 A f) (@lem3699402 A f)). Qed.
Lemma lem3699606 {A : Type'} (f : A -> A) : (term139 A f) = (term187 A f).
Proof. exact (TRANS (@lem3699398 A f) (@lem3699425 A f)). Qed.
Lemma lem3699607 {A : Type'} : (term140 A) = (term188 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699606 A f)). Qed.
Lemma lem3699608 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699609 {A : Type'} : (term141 A) = (term189 A).
Proof. exact (MK_COMB (@lem3699608 A) (@lem3699607 A)). Qed.
Lemma lem3699611 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3699612 {A : Type'} (P : type488 A) (Q : type488 A) : (term190 A P Q) = (term191 A P Q).
Proof. exact (@lem3699611 (A -> A) P Q). Qed.
Lemma lem3699613 {A : Type'} : (term192 A) = (term193 A).
Proof. exact (@lem3699612 A (term194 A) (term195 A)). Qed.
Lemma lem3699614 {A : Type'} (f : A -> A) : (term196 A f) = (term181 A f).
Proof. exact (eq_refl (term196 A f)). Qed.
Lemma lem3699615 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699616 {A : Type'} (f : A -> A) : (term197 A f) = (term183 A f).
Proof. exact (MK_COMB (@lem3699615) (@lem3699614 A f)). Qed.
Lemma lem3699617 {A : Type'} (f : A -> A) : (term198 A f) = (term186 A f).
Proof. exact (eq_refl (term198 A f)). Qed.
Lemma lem3699618 {A : Type'} (f : A -> A) : (term199 A f) = (term187 A f).
Proof. exact (MK_COMB (@lem3699616 A f) (@lem3699617 A f)). Qed.
Lemma lem3699619 {A : Type'} : (term200 A) = (term188 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699618 A f)). Qed.
Lemma lem3699620 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699621 {A : Type'} : (term192 A) = (term189 A).
Proof. exact (MK_COMB (@lem3699620 A) (@lem3699619 A)). Qed.
Lemma lem3699622 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699623 {A : Type'} : (term201 A) = (term202 A).
Proof. exact (MK_COMB (@lem3699622) (@lem3699621 A)). Qed.
Lemma lem3699624 {A : Type'} (f : A -> A) : (term196 A f) = (term181 A f).
Proof. exact (eq_refl (term196 A f)). Qed.
Lemma lem3699625 {A : Type'} : (term203 A) = (term194 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699624 A f)). Qed.
Lemma lem3699626 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699627 {A : Type'} : (term204 A) = (term205 A).
Proof. exact (MK_COMB (@lem3699626 A) (@lem3699625 A)). Qed.
Lemma lem3699628 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3699629 {A : Type'} : (term206 A) = (term207 A).
Proof. exact (MK_COMB (@lem3699628) (@lem3699627 A)). Qed.
Lemma lem3699630 {A : Type'} (f : A -> A) : (term198 A f) = (term186 A f).
Proof. exact (eq_refl (term198 A f)). Qed.
Lemma lem3699631 {A : Type'} : (term208 A) = (term195 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699630 A f)). Qed.
Lemma lem3699632 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699633 {A : Type'} : (term209 A) = (term210 A).
Proof. exact (MK_COMB (@lem3699632 A) (@lem3699631 A)). Qed.
Lemma lem3699634 {A : Type'} : (term193 A) = (term211 A).
Proof. exact (MK_COMB (@lem3699629 A) (@lem3699633 A)). Qed.
Lemma lem3699635 {A : Type'} : ((term192 A) = (term193 A)) = ((term189 A) = (term211 A)).
Proof. exact (MK_COMB (@lem3699623 A) (@lem3699634 A)). Qed.
Lemma lem3699636 {A : Type'} : (term189 A) = (term211 A).
Proof. exact (EQ_MP (@lem3699635 A) (@lem3699613 A)). Qed.
Lemma lem3699825 {A : Type'} : (term141 A) = (term211 A).
Proof. exact (TRANS (@lem3699609 A) (@lem3699636 A)). Qed.
Lemma lem3699827 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3699828 {A : Type'} (P : Prop) (Q : type686 A) : (term214 A P Q) = (term215 A P Q).
Proof. exact (@lem3699827 (A -> Prop) P Q). Qed.
Lemma lem3699829 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term216 A s t f) = (term217 A s t f).
Proof. exact (@lem3699828 A (term110 A t f s) (term35 A s t f)). Qed.
Lemma lem3699830 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term120 A s t f s') = (term34 A s t f s').
Proof. exact (eq_refl (term120 A s t f s')). Qed.
Lemma lem3699831 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term218 A s t f) = (term35 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3699830 A s t f s')). Qed.
Lemma lem3699832 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3699833 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term219 A s t f) = (term36 A s t f).
Proof. exact (MK_COMB (@lem3699832 A) (@lem3699831 A s t f)). Qed.
Lemma lem3699834 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term126 A t f s) = (term126 A t f s).
Proof. exact (eq_refl (term126 A t f s)). Qed.
Lemma lem3699835 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term216 A s t f) = (term128 A s t f).
Proof. exact (MK_COMB (@lem3699834 A t f s) (@lem3699833 A s t f)). Qed.
Lemma lem3699836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699837 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term220 A s t f) = (term221 A s t f).
Proof. exact (MK_COMB (@lem3699836) (@lem3699835 A s t f)). Qed.
Lemma lem3699838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term120 A s t f s') = (term34 A s t f s').
Proof. exact (eq_refl (term120 A s t f s')). Qed.
Lemma lem3699839 {A : Type'} (t : A -> Prop) (f : A -> A) (s : A -> Prop) : (term126 A t f s) = (term126 A t f s).
Proof. exact (eq_refl (term126 A t f s)). Qed.
Lemma lem3699840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term222 A s t f s') = (term223 A s t f s').
Proof. exact (MK_COMB (@lem3699839 A t f s) (@lem3699838 A s t f s')). Qed.
Lemma lem3699841 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term224 A s t f) = (term225 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3699840 A s t f s')). Qed.
Lemma lem3699842 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3699843 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term217 A s t f) = (term226 A s t f).
Proof. exact (MK_COMB (@lem3699842 A) (@lem3699841 A s t f)). Qed.
Lemma lem3699844 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : ((term216 A s t f) = (term217 A s t f)) = ((term128 A s t f) = (term226 A s t f)).
Proof. exact (MK_COMB (@lem3699837 A s t f) (@lem3699843 A s t f)). Qed.
Lemma lem3699845 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term128 A s t f) = (term226 A s t f).
Proof. exact (EQ_MP (@lem3699844 A s t f) (@lem3699829 A s t f)). Qed.
Lemma lem3699846 {A : Type'} (s : A -> Prop) (f : A -> A) : (term149 A s f) = (term227 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699845 A s t f)). Qed.
Lemma lem3699847 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699848 {A : Type'} (s : A -> Prop) (f : A -> A) : (term164 A s f) = (term228 A s f).
Proof. exact (MK_COMB (@lem3699847 A) (@lem3699846 A s f)). Qed.
Lemma lem3699850 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3699851 {A : Type'} (P : type639 A) : (term231 A P) = (term232 A P).
Proof. exact (@lem3699850 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem3699852 {A : Type'} (s : A -> Prop) (f : A -> A) : (term233 A s f) = (term234 A s f).
Proof. exact (@lem3699851 A (term235 A s f)). Qed.
Lemma lem3699853 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term236 A s f t) = (term225 A s t f).
Proof. exact (eq_refl (term236 A s f t)). Qed.
Lemma lem3699854 {A : Type'} (s' : A -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3699855 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term237 A s f t s') = (term238 A s t f s').
Proof. exact (MK_COMB (@lem3699853 A s t f) (@lem3699854 A s')). Qed.
Lemma lem3699856 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term238 A s t f s') = (term223 A s t f s').
Proof. exact (eq_refl (term238 A s t f s')). Qed.
Lemma lem3699857 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) (s' : A -> Prop) : (term237 A s f t s') = (term223 A s t f s').
Proof. exact (TRANS (@lem3699855 A s t f s') (@lem3699856 A s t f s')). Qed.
Lemma lem3699858 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term239 A s f t) = (term225 A s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3699857 A s t f s')). Qed.
Lemma lem3699859 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3699860 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term240 A s f t) = (term226 A s t f).
Proof. exact (MK_COMB (@lem3699859 A) (@lem3699858 A s t f)). Qed.
Lemma lem3699861 {A : Type'} (s : A -> Prop) (f : A -> A) : (term241 A s f) = (term227 A s f).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699860 A s t f)). Qed.
Lemma lem3699862 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699863 {A : Type'} (s : A -> Prop) (f : A -> A) : (term233 A s f) = (term228 A s f).
Proof. exact (MK_COMB (@lem3699862 A) (@lem3699861 A s f)). Qed.
Lemma lem3699864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699865 {A : Type'} (s : A -> Prop) (f : A -> A) : (term242 A s f) = (term243 A s f).
Proof. exact (MK_COMB (@lem3699864) (@lem3699863 A s f)). Qed.
Lemma lem3699866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (f : A -> A) : (term236 A s f t) = (term225 A s t f).
Proof. exact (eq_refl (term236 A s f t)). Qed.
Lemma lem3699867 {A : Type'} (s' : type672 A) (t : A -> Prop) : (s' t) = (s' t).
Proof. exact (eq_refl (s' t)). Qed.
Lemma lem3699868 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) (t : A -> Prop) : (term244 A s f s' t) = (term245 A s f s' t).
Proof. exact (MK_COMB (@lem3699866 A s t f) (@lem3699867 A s' t)). Qed.
Lemma lem3699869 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) (t : A -> Prop) : (term245 A s f s' t) = (term246 A s f s' t).
Proof. exact (eq_refl (term245 A s f s' t)). Qed.
Lemma lem3699870 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) (t : A -> Prop) : (term244 A s f s' t) = (term246 A s f s' t).
Proof. exact (TRANS (@lem3699868 A s f s' t) (@lem3699869 A s f s' t)). Qed.
Lemma lem3699871 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term247 A s f s') = (term248 A s f s').
Proof. exact (fun_ext (fun t : A -> Prop => @lem3699870 A s f s' t)). Qed.
Lemma lem3699872 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699873 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term249 A s f s') = (term250 A s f s').
Proof. exact (MK_COMB (@lem3699872 A) (@lem3699871 A s f s')). Qed.
Lemma lem3699874 {A : Type'} (s : A -> Prop) (f : A -> A) : (term251 A s f) = (term252 A s f).
Proof. exact (fun_ext (fun s' : type672 A => @lem3699873 A s f s')). Qed.
Lemma lem3699875 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699876 {A : Type'} (s : A -> Prop) (f : A -> A) : (term234 A s f) = (term253 A s f).
Proof. exact (MK_COMB (@lem3699875 A) (@lem3699874 A s f)). Qed.
Lemma lem3699877 {A : Type'} (s : A -> Prop) (f : A -> A) : ((term233 A s f) = (term234 A s f)) = ((term228 A s f) = (term253 A s f)).
Proof. exact (MK_COMB (@lem3699865 A s f) (@lem3699876 A s f)). Qed.
Lemma lem3699878 {A : Type'} (s : A -> Prop) (f : A -> A) : (term228 A s f) = (term253 A s f).
Proof. exact (EQ_MP (@lem3699877 A s f) (@lem3699852 A s f)). Qed.
Lemma lem3699879 {A : Type'} (s : A -> Prop) (f : A -> A) : (term164 A s f) = (term253 A s f).
Proof. exact (TRANS (@lem3699848 A s f) (@lem3699878 A s f)). Qed.
Lemma lem3699880 {A : Type'} (f : A -> A) : (term171 A f) = (term254 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699879 A s f)). Qed.
Lemma lem3699881 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699882 {A : Type'} (f : A -> A) : (term186 A f) = (term255 A f).
Proof. exact (MK_COMB (@lem3699881 A) (@lem3699880 A f)). Qed.
Lemma lem3699884 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3699885 {A : Type'} (P : type596 A) : (term256 A P) = (term257 A P).
Proof. exact (@lem3699884 (A -> Prop) (type672 A) P). Qed.
Lemma lem3699886 {A : Type'} (f : A -> A) : (term258 A f) = (term259 A f).
Proof. exact (@lem3699885 A (term260 A f)). Qed.
Lemma lem3699887 {A : Type'} (s : A -> Prop) (f : A -> A) : (term261 A f s) = (term252 A s f).
Proof. exact (eq_refl (term261 A f s)). Qed.
Lemma lem3699888 {A : Type'} (s' : type672 A) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3699889 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term262 A f s s') = (term263 A s f s').
Proof. exact (MK_COMB (@lem3699887 A s f) (@lem3699888 A s')). Qed.
Lemma lem3699890 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term263 A s f s') = (term250 A s f s').
Proof. exact (eq_refl (term263 A s f s')). Qed.
Lemma lem3699891 {A : Type'} (s : A -> Prop) (f : A -> A) (s' : type672 A) : (term262 A f s s') = (term250 A s f s').
Proof. exact (TRANS (@lem3699889 A s f s') (@lem3699890 A s f s')). Qed.
Lemma lem3699892 {A : Type'} (s : A -> Prop) (f : A -> A) : (term264 A f s) = (term252 A s f).
Proof. exact (fun_ext (fun s' : type672 A => @lem3699891 A s f s')). Qed.
Lemma lem3699893 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699894 {A : Type'} (s : A -> Prop) (f : A -> A) : (term265 A f s) = (term253 A s f).
Proof. exact (MK_COMB (@lem3699893 A) (@lem3699892 A s f)). Qed.
Lemma lem3699895 {A : Type'} (f : A -> A) : (term266 A f) = (term254 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699894 A s f)). Qed.
Lemma lem3699896 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699897 {A : Type'} (f : A -> A) : (term258 A f) = (term255 A f).
Proof. exact (MK_COMB (@lem3699896 A) (@lem3699895 A f)). Qed.
Lemma lem3699898 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699899 {A : Type'} (f : A -> A) : (term267 A f) = (term268 A f).
Proof. exact (MK_COMB (@lem3699898) (@lem3699897 A f)). Qed.
Lemma lem3699900 {A : Type'} (s : A -> Prop) (f : A -> A) : (term261 A f s) = (term252 A s f).
Proof. exact (eq_refl (term261 A f s)). Qed.
Lemma lem3699901 {A : Type'} (s' : type636 A) (s : A -> Prop) : (s' s) = (s' s).
Proof. exact (eq_refl (s' s)). Qed.
Lemma lem3699902 {A : Type'} (f : A -> A) (s' : type636 A) (s : A -> Prop) : (term269 A f s' s) = (term270 A f s' s).
Proof. exact (MK_COMB (@lem3699900 A s f) (@lem3699901 A s' s)). Qed.
Lemma lem3699903 {A : Type'} (f : A -> A) (s' : type636 A) (s : A -> Prop) : (term270 A f s' s) = (term271 A f s' s).
Proof. exact (eq_refl (term270 A f s' s)). Qed.
Lemma lem3699904 {A : Type'} (f : A -> A) (s' : type636 A) (s : A -> Prop) : (term269 A f s' s) = (term271 A f s' s).
Proof. exact (TRANS (@lem3699902 A f s' s) (@lem3699903 A f s' s)). Qed.
Lemma lem3699905 {A : Type'} (f : A -> A) (s' : type636 A) : (term272 A f s') = (term273 A f s').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3699904 A f s' s)). Qed.
Lemma lem3699906 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3699907 {A : Type'} (f : A -> A) (s' : type636 A) : (term274 A f s') = (term275 A f s').
Proof. exact (MK_COMB (@lem3699906 A) (@lem3699905 A f s')). Qed.
Lemma lem3699908 {A : Type'} (f : A -> A) : (term276 A f) = (term277 A f).
Proof. exact (fun_ext (fun s' : type636 A => @lem3699907 A f s')). Qed.
Lemma lem3699909 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699910 {A : Type'} (f : A -> A) : (term259 A f) = (term278 A f).
Proof. exact (MK_COMB (@lem3699909 A) (@lem3699908 A f)). Qed.
Lemma lem3699911 {A : Type'} (f : A -> A) : ((term258 A f) = (term259 A f)) = ((term255 A f) = (term278 A f)).
Proof. exact (MK_COMB (@lem3699899 A f) (@lem3699910 A f)). Qed.
Lemma lem3699912 {A : Type'} (f : A -> A) : (term255 A f) = (term278 A f).
Proof. exact (EQ_MP (@lem3699911 A f) (@lem3699886 A f)). Qed.
Lemma lem3699913 {A : Type'} (f : A -> A) : (term186 A f) = (term278 A f).
Proof. exact (TRANS (@lem3699882 A f) (@lem3699912 A f)). Qed.
Lemma lem3699914 {A : Type'} : (term195 A) = (term279 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699913 A f)). Qed.
Lemma lem3699915 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699916 {A : Type'} : (term210 A) = (term280 A).
Proof. exact (MK_COMB (@lem3699915 A) (@lem3699914 A)). Qed.
Lemma lem3699918 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3699919 {A : Type'} (P : type480 A) : (term281 A P) = (term282 A P).
Proof. exact (@lem3699918 (A -> A) (type636 A) P). Qed.
Lemma lem3699920 {A : Type'} : (term283 A) = (term284 A).
Proof. exact (@lem3699919 A (term285 A)). Qed.
Lemma lem3699921 {A : Type'} (f : A -> A) : (term286 A f) = (term277 A f).
Proof. exact (eq_refl (term286 A f)). Qed.
Lemma lem3699922 {A : Type'} (s' : type636 A) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3699923 {A : Type'} (f : A -> A) (s' : type636 A) : (term287 A f s') = (term288 A f s').
Proof. exact (MK_COMB (@lem3699921 A f) (@lem3699922 A s')). Qed.
Lemma lem3699924 {A : Type'} (f : A -> A) (s' : type636 A) : (term288 A f s') = (term275 A f s').
Proof. exact (eq_refl (term288 A f s')). Qed.
Lemma lem3699925 {A : Type'} (f : A -> A) (s' : type636 A) : (term287 A f s') = (term275 A f s').
Proof. exact (TRANS (@lem3699923 A f s') (@lem3699924 A f s')). Qed.
Lemma lem3699926 {A : Type'} (f : A -> A) : (term289 A f) = (term277 A f).
Proof. exact (fun_ext (fun s' : type636 A => @lem3699925 A f s')). Qed.
Lemma lem3699927 {A : Type'} : (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699928 {A : Type'} (f : A -> A) : (term290 A f) = (term278 A f).
Proof. exact (MK_COMB (@lem3699927 A) (@lem3699926 A f)). Qed.
Lemma lem3699929 {A : Type'} : (term291 A) = (term279 A).
Proof. exact (fun_ext (fun f : A -> A => @lem3699928 A f)). Qed.
Lemma lem3699930 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699931 {A : Type'} : (term283 A) = (term280 A).
Proof. exact (MK_COMB (@lem3699930 A) (@lem3699929 A)). Qed.
Lemma lem3699932 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699933 {A : Type'} : (term292 A) = (term293 A).
Proof. exact (MK_COMB (@lem3699932) (@lem3699931 A)). Qed.
Lemma lem3699934 {A : Type'} (f : A -> A) : (term286 A f) = (term277 A f).
Proof. exact (eq_refl (term286 A f)). Qed.
Lemma lem3699935 {A : Type'} (s' : type483 A) (f : A -> A) : (s' f) = (s' f).
Proof. exact (eq_refl (s' f)). Qed.
Lemma lem3699936 {A : Type'} (s' : type483 A) (f : A -> A) : (term294 A s' f) = (term295 A s' f).
Proof. exact (MK_COMB (@lem3699934 A f) (@lem3699935 A s' f)). Qed.
Lemma lem3699937 {A : Type'} (s' : type483 A) (f : A -> A) : (term295 A s' f) = (term296 A s' f).
Proof. exact (eq_refl (term295 A s' f)). Qed.
Lemma lem3699938 {A : Type'} (s' : type483 A) (f : A -> A) : (term294 A s' f) = (term296 A s' f).
Proof. exact (TRANS (@lem3699936 A s' f) (@lem3699937 A s' f)). Qed.
Lemma lem3699939 {A : Type'} (s' : type483 A) : (term297 A s') = (term298 A s').
Proof. exact (fun_ext (fun f : A -> A => @lem3699938 A s' f)). Qed.
Lemma lem3699940 {A : Type'} : (@all (A -> A)) = (@all (A -> A)).
Proof. exact (eq_refl (@all (A -> A))). Qed.
Lemma lem3699941 {A : Type'} (s' : type483 A) : (term299 A s') = (term300 A s').
Proof. exact (MK_COMB (@lem3699940 A) (@lem3699939 A s')). Qed.
Lemma lem3699942 {A : Type'} : (term301 A) = (term302 A).
Proof. exact (fun_ext (fun s' : type483 A => @lem3699941 A s')). Qed.
Lemma lem3699943 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699944 {A : Type'} : (term284 A) = (term303 A).
Proof. exact (MK_COMB (@lem3699943 A) (@lem3699942 A)). Qed.
Lemma lem3699945 {A : Type'} : ((term283 A) = (term284 A)) = ((term280 A) = (term303 A)).
Proof. exact (MK_COMB (@lem3699933 A) (@lem3699944 A)). Qed.
Lemma lem3699946 {A : Type'} : (term280 A) = (term303 A).
Proof. exact (EQ_MP (@lem3699945 A) (@lem3699920 A)). Qed.
Lemma lem3699947 {A : Type'} : (term210 A) = (term303 A).
Proof. exact (TRANS (@lem3699916 A) (@lem3699946 A)). Qed.
Lemma lem3699948 {A : Type'} : (term207 A) = (term207 A).
Proof. exact (eq_refl (term207 A)). Qed.
Lemma lem3699949 {A : Type'} : (term211 A) = (term304 A).
Proof. exact (MK_COMB (@lem3699948 A) (@lem3699947 A)). Qed.
Lemma lem3699951 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3699952 {A : Type'} (P : Prop) (Q : type92 A) : (term307 A P Q) = (term308 A P Q).
Proof. exact (@lem3699951 (type483 A) P Q). Qed.
Lemma lem3699953 {A : Type'} : (term309 A) = (term310 A).
Proof. exact (@lem3699952 A (term205 A) (term302 A)). Qed.
Lemma lem3699954 {A : Type'} (s' : type483 A) : (term311 A s') = (term300 A s').
Proof. exact (eq_refl (term311 A s')). Qed.
Lemma lem3699955 {A : Type'} : (term312 A) = (term302 A).
Proof. exact (fun_ext (fun s' : type483 A => @lem3699954 A s')). Qed.
Lemma lem3699956 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699957 {A : Type'} : (term313 A) = (term303 A).
Proof. exact (MK_COMB (@lem3699956 A) (@lem3699955 A)). Qed.
Lemma lem3699958 {A : Type'} : (term207 A) = (term207 A).
Proof. exact (eq_refl (term207 A)). Qed.
Lemma lem3699959 {A : Type'} : (term309 A) = (term304 A).
Proof. exact (MK_COMB (@lem3699958 A) (@lem3699957 A)). Qed.
Lemma lem3699960 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3699961 {A : Type'} : (term314 A) = (term315 A).
Proof. exact (MK_COMB (@lem3699960) (@lem3699959 A)). Qed.
Lemma lem3699962 {A : Type'} (s' : type483 A) : (term311 A s') = (term300 A s').
Proof. exact (eq_refl (term311 A s')). Qed.
Lemma lem3699963 {A : Type'} : (term207 A) = (term207 A).
Proof. exact (eq_refl (term207 A)). Qed.
Lemma lem3699964 {A : Type'} (s' : type483 A) : (term316 A s') = (term317 A s').
Proof. exact (MK_COMB (@lem3699963 A) (@lem3699962 A s')). Qed.
Lemma lem3699965 {A : Type'} : (term318 A) = (term319 A).
Proof. exact (fun_ext (fun s' : type483 A => @lem3699964 A s')). Qed.
Lemma lem3699966 {A : Type'} : (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)) = (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> A) -> (A -> Prop) -> (A -> Prop) -> A -> Prop))). Qed.
Lemma lem3699967 {A : Type'} : (term310 A) = (term320 A).
Proof. exact (MK_COMB (@lem3699966 A) (@lem3699965 A)). Qed.
Lemma lem3699968 {A : Type'} : ((term309 A) = (term310 A)) = ((term304 A) = (term320 A)).
Proof. exact (MK_COMB (@lem3699961 A) (@lem3699967 A)). Qed.
Lemma lem3699969 {A : Type'} : (term304 A) = (term320 A).
Proof. exact (EQ_MP (@lem3699968 A) (@lem3699953 A)). Qed.
Lemma lem3699970 {A : Type'} : (term211 A) = (term320 A).
Proof. exact (TRANS (@lem3699949 A) (@lem3699969 A)). Qed.
Lemma lem3699971 {A : Type'} : (term141 A) = (term320 A).
Proof. exact (TRANS (@lem3699825 A) (@lem3699970 A)). Qed.
Lemma lem3699972 {A : Type'} : (term13 A) = (term320 A).
Proof. exact (TRANS (@lem3699188 A) (@lem3699971 A)). Qed.
Lemma lem3699973 {A : Type'} (h1 : term13 A) : term320 A.
Proof. exact (EQ_MP (@lem3699972 A) (@lem3698945 A h1)). Qed.
Lemma lem3699982 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term321 A B t f s) = (term322 A B t f s).
Proof. exact (@lem17045 (@FINITE B t) (term66 A B t f s)). Qed.
Lemma lem3699996 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term323 A B s t f s') = (term324 A B s t f s').
Proof. exact (@lem17045 (@SUBSET A s' s) (t = (@IMAGE A B f s'))). Qed.
Lemma lem3700001 {A : Type'} (s' : A -> Prop) : (term67 A s') = (term67 A s').
Proof. exact (eq_refl (term67 A s')). Qed.
Lemma lem3700002 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term325 A B s t f s') = (term326 A B s t f s').
Proof. exact (MK_COMB (@lem3700001 A s') (@lem3699996 A B s t f s')). Qed.
Lemma lem3700003 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term327 A B s t f s') = (term325 A B s t f s').
Proof. exact (@lem17045 (@FINITE A s') (term328 A B s t f s')). Qed.
Lemma lem3700004 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term327 A B s t f s') = (term326 A B s t f s').
Proof. exact (TRANS (@lem3700003 A B s t f s') (@lem3700002 A B s t f s')). Qed.
Lemma lem3700007 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term44 A B s t f s') = (term44 A B s t f s').
Proof. exact (eq_refl (term44 A B s t f s')). Qed.
Lemma lem3700008 {A : Type'} (P : type686 A) : (term72 A P) = (term73 A P).
Proof. exact (@lem18394 (A -> Prop) P). Qed.
Lemma lem3700009 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term329 A B s t f) = (term330 A B s t f).
Proof. exact (@lem3700008 A (term45 A B s t f)). Qed.
Lemma lem3700010 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term331 A B s t f s') = (term44 A B s t f s').
Proof. exact (eq_refl (term331 A B s t f s')). Qed.
Lemma lem3700011 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3700012 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term332 A B s t f s') = (term327 A B s t f s').
Proof. exact (MK_COMB (@lem3700011) (@lem3700010 A B s t f s')). Qed.
Lemma lem3700013 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term332 A B s t f s') = (term326 A B s t f s').
Proof. exact (TRANS (@lem3700012 A B s t f s') (@lem3700004 A B s t f s')). Qed.
Lemma lem3700014 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term333 A B s t f) = (term334 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3700013 A B s t f s')). Qed.
Lemma lem3700015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700016 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term330 A B s t f) = (term335 A B s t f).
Proof. exact (MK_COMB (@lem3700015 A) (@lem3700014 A B s t f)). Qed.
Lemma lem3700017 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term329 A B s t f) = (term335 A B s t f).
Proof. exact (TRANS (@lem3700009 A B s t f) (@lem3700016 A B s t f)). Qed.
Lemma lem3700018 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term45 A B s t f) = (term45 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3700007 A B s t f s')). Qed.
Lemma lem3700019 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3700020 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term46 A B s t f) = (term46 A B s t f).
Proof. exact (MK_COMB (@lem3700019 A) (@lem3700018 A B s t f)). Qed.
Lemma lem3700021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3700022 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term336 A B t f s) = (term337 A B t f s).
Proof. exact (MK_COMB (@lem3700021) (@lem3699982 A B t f s)). Qed.
Lemma lem3700023 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term338 A B s t f) = (term339 A B s t f).
Proof. exact (MK_COMB (@lem3700022 A B t f s) (@lem3700020 A B s t f)). Qed.
Lemma lem3700025 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term340 A B t f s) = (term340 A B t f s).
Proof. exact (eq_refl (term340 A B t f s)). Qed.
Lemma lem3700026 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term341 A B s t f) = (term342 A B s t f).
Proof. exact (MK_COMB (@lem3700025 A B t f s) (@lem3700017 A B s t f)). Qed.
Lemma lem3700027 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700028 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term343 A B s t f) = (term344 A B s t f).
Proof. exact (MK_COMB (@lem3700027) (@lem3700026 A B s t f)). Qed.
Lemma lem3700029 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term345 A B s t f) = (term346 A B s t f).
Proof. exact (MK_COMB (@lem3700028 A B s t f) (@lem3700023 A B s t f)). Qed.
Lemma lem3700030 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term48 A B t f s) = (term46 A B s t f)) = (term345 A B s t f).
Proof. exact (@lem17784 (term48 A B t f s) (term46 A B s t f)). Qed.
Lemma lem3700031 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term48 A B t f s) = (term46 A B s t f)) = (term346 A B s t f).
Proof. exact (TRANS (@lem3700030 A B s t f) (@lem3700029 A B s t f)). Qed.
Lemma lem3700032 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term49 A B s f) = (term347 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700031 A B s t f)). Qed.
Lemma lem3700033 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700034 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term50 A B s f) = (term348 A B s f).
Proof. exact (MK_COMB (@lem3700033 B) (@lem3700032 A B s f)). Qed.
Lemma lem3700035 {A B : Type'} (f : A -> B) : (term51 A B f) = (term349 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700034 A B s f)). Qed.
Lemma lem3700036 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700037 {A B : Type'} (f : A -> B) : (term52 A B f) = (term350 A B f).
Proof. exact (MK_COMB (@lem3700036 A) (@lem3700035 A B f)). Qed.
Lemma lem3700038 {A B : Type'} : (term53 A B) = (term351 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700037 A B f)). Qed.
Lemma lem3700039 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700040 {A B : Type'} : (term12 A B) = (term352 A B).
Proof. exact (MK_COMB (@lem3700039 A B) (@lem3700038 A B)). Qed.
Lemma lem3700050 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3700051 {B : Type'} (P : type686 B) (Q : type686 B) : (term144 B P Q) = (term145 B P Q).
Proof. exact (@lem3700050 (B -> Prop) P Q). Qed.
Lemma lem3700052 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term353 A B s f) = (term354 A B s f).
Proof. exact (@lem3700051 B (term355 A B s f) (term356 A B s f)). Qed.
Lemma lem3700053 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term357 A B s f t) = (term342 A B s t f).
Proof. exact (eq_refl (term357 A B s f t)). Qed.
Lemma lem3700054 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700055 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term358 A B s f t) = (term344 A B s t f).
Proof. exact (MK_COMB (@lem3700054) (@lem3700053 A B s t f)). Qed.
Lemma lem3700056 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term359 A B s f t) = (term339 A B s t f).
Proof. exact (eq_refl (term359 A B s f t)). Qed.
Lemma lem3700057 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term360 A B s f t) = (term346 A B s t f).
Proof. exact (MK_COMB (@lem3700055 A B s t f) (@lem3700056 A B s t f)). Qed.
Lemma lem3700058 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term361 A B s f) = (term347 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700057 A B s t f)). Qed.
Lemma lem3700059 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700060 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term353 A B s f) = (term348 A B s f).
Proof. exact (MK_COMB (@lem3700059 B) (@lem3700058 A B s f)). Qed.
Lemma lem3700061 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700062 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term362 A B s f) = (term363 A B s f).
Proof. exact (MK_COMB (@lem3700061) (@lem3700060 A B s f)). Qed.
Lemma lem3700063 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term357 A B s f t) = (term342 A B s t f).
Proof. exact (eq_refl (term357 A B s f t)). Qed.
Lemma lem3700064 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term364 A B s f) = (term355 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700063 A B s t f)). Qed.
Lemma lem3700065 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700066 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term365 A B s f) = (term366 A B s f).
Proof. exact (MK_COMB (@lem3700065 B) (@lem3700064 A B s f)). Qed.
Lemma lem3700067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700068 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term367 A B s f) = (term368 A B s f).
Proof. exact (MK_COMB (@lem3700067) (@lem3700066 A B s f)). Qed.
Lemma lem3700069 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term359 A B s f t) = (term339 A B s t f).
Proof. exact (eq_refl (term359 A B s f t)). Qed.
Lemma lem3700070 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term369 A B s f) = (term356 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700069 A B s t f)). Qed.
Lemma lem3700071 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700072 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term370 A B s f) = (term371 A B s f).
Proof. exact (MK_COMB (@lem3700071 B) (@lem3700070 A B s f)). Qed.
Lemma lem3700073 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term354 A B s f) = (term372 A B s f).
Proof. exact (MK_COMB (@lem3700068 A B s f) (@lem3700072 A B s f)). Qed.
Lemma lem3700074 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term353 A B s f) = (term354 A B s f)) = ((term348 A B s f) = (term372 A B s f)).
Proof. exact (MK_COMB (@lem3700062 A B s f) (@lem3700073 A B s f)). Qed.
Lemma lem3700075 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term348 A B s f) = (term372 A B s f).
Proof. exact (EQ_MP (@lem3700074 A B s f) (@lem3700052 A B s f)). Qed.
Lemma lem3700248 {A B : Type'} (f : A -> B) : (term349 A B f) = (term373 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700075 A B s f)). Qed.
Lemma lem3700249 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700250 {A B : Type'} (f : A -> B) : (term350 A B f) = (term374 A B f).
Proof. exact (MK_COMB (@lem3700249 A) (@lem3700248 A B f)). Qed.
Lemma lem3700252 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3700253 {A : Type'} (P : type686 A) (Q : type686 A) : (term144 A P Q) = (term145 A P Q).
Proof. exact (@lem3700252 (A -> Prop) P Q). Qed.
Lemma lem3700254 {A B : Type'} (f : A -> B) : (term375 A B f) = (term376 A B f).
Proof. exact (@lem3700253 A (term377 A B f) (term378 A B f)). Qed.
Lemma lem3700255 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term379 A B f s) = (term366 A B s f).
Proof. exact (eq_refl (term379 A B f s)). Qed.
Lemma lem3700256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700257 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term380 A B f s) = (term368 A B s f).
Proof. exact (MK_COMB (@lem3700256) (@lem3700255 A B s f)). Qed.
Lemma lem3700258 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term381 A B f s) = (term371 A B s f).
Proof. exact (eq_refl (term381 A B f s)). Qed.
Lemma lem3700259 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term382 A B f s) = (term372 A B s f).
Proof. exact (MK_COMB (@lem3700257 A B s f) (@lem3700258 A B s f)). Qed.
Lemma lem3700260 {A B : Type'} (f : A -> B) : (term383 A B f) = (term373 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700259 A B s f)). Qed.
Lemma lem3700261 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700262 {A B : Type'} (f : A -> B) : (term375 A B f) = (term374 A B f).
Proof. exact (MK_COMB (@lem3700261 A) (@lem3700260 A B f)). Qed.
Lemma lem3700263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700264 {A B : Type'} (f : A -> B) : (term384 A B f) = (term385 A B f).
Proof. exact (MK_COMB (@lem3700263) (@lem3700262 A B f)). Qed.
Lemma lem3700265 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term379 A B f s) = (term366 A B s f).
Proof. exact (eq_refl (term379 A B f s)). Qed.
Lemma lem3700266 {A B : Type'} (f : A -> B) : (term386 A B f) = (term377 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700265 A B s f)). Qed.
Lemma lem3700267 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700268 {A B : Type'} (f : A -> B) : (term387 A B f) = (term388 A B f).
Proof. exact (MK_COMB (@lem3700267 A) (@lem3700266 A B f)). Qed.
Lemma lem3700269 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700270 {A B : Type'} (f : A -> B) : (term389 A B f) = (term390 A B f).
Proof. exact (MK_COMB (@lem3700269) (@lem3700268 A B f)). Qed.
Lemma lem3700271 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term381 A B f s) = (term371 A B s f).
Proof. exact (eq_refl (term381 A B f s)). Qed.
Lemma lem3700272 {A B : Type'} (f : A -> B) : (term391 A B f) = (term378 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700271 A B s f)). Qed.
Lemma lem3700273 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700274 {A B : Type'} (f : A -> B) : (term392 A B f) = (term393 A B f).
Proof. exact (MK_COMB (@lem3700273 A) (@lem3700272 A B f)). Qed.
Lemma lem3700275 {A B : Type'} (f : A -> B) : (term376 A B f) = (term394 A B f).
Proof. exact (MK_COMB (@lem3700270 A B f) (@lem3700274 A B f)). Qed.
Lemma lem3700276 {A B : Type'} (f : A -> B) : ((term375 A B f) = (term376 A B f)) = ((term374 A B f) = (term394 A B f)).
Proof. exact (MK_COMB (@lem3700264 A B f) (@lem3700275 A B f)). Qed.
Lemma lem3700277 {A B : Type'} (f : A -> B) : (term374 A B f) = (term394 A B f).
Proof. exact (EQ_MP (@lem3700276 A B f) (@lem3700254 A B f)). Qed.
Lemma lem3700458 {A B : Type'} (f : A -> B) : (term350 A B f) = (term394 A B f).
Proof. exact (TRANS (@lem3700250 A B f) (@lem3700277 A B f)). Qed.
Lemma lem3700459 {A B : Type'} : (term351 A B) = (term395 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700458 A B f)). Qed.
Lemma lem3700460 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700461 {A B : Type'} : (term352 A B) = (term396 A B).
Proof. exact (MK_COMB (@lem3700460 A B) (@lem3700459 A B)). Qed.
Lemma lem3700463 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3700464 {A B : Type'} (P : type572 A B) (Q : type572 A B) : (term397 A B P Q) = (term398 A B P Q).
Proof. exact (@lem3700463 (A -> B) P Q). Qed.
Lemma lem3700465 {A B : Type'} : (term399 A B) = (term400 A B).
Proof. exact (@lem3700464 A B (term401 A B) (term402 A B)). Qed.
Lemma lem3700466 {A B : Type'} (f : A -> B) : (term403 A B f) = (term388 A B f).
Proof. exact (eq_refl (term403 A B f)). Qed.
Lemma lem3700467 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700468 {A B : Type'} (f : A -> B) : (term404 A B f) = (term390 A B f).
Proof. exact (MK_COMB (@lem3700467) (@lem3700466 A B f)). Qed.
Lemma lem3700469 {A B : Type'} (f : A -> B) : (term405 A B f) = (term393 A B f).
Proof. exact (eq_refl (term405 A B f)). Qed.
Lemma lem3700470 {A B : Type'} (f : A -> B) : (term406 A B f) = (term394 A B f).
Proof. exact (MK_COMB (@lem3700468 A B f) (@lem3700469 A B f)). Qed.
Lemma lem3700471 {A B : Type'} : (term407 A B) = (term395 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700470 A B f)). Qed.
Lemma lem3700472 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700473 {A B : Type'} : (term399 A B) = (term396 A B).
Proof. exact (MK_COMB (@lem3700472 A B) (@lem3700471 A B)). Qed.
Lemma lem3700474 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700475 {A B : Type'} : (term408 A B) = (term409 A B).
Proof. exact (MK_COMB (@lem3700474) (@lem3700473 A B)). Qed.
Lemma lem3700476 {A B : Type'} (f : A -> B) : (term403 A B f) = (term388 A B f).
Proof. exact (eq_refl (term403 A B f)). Qed.
Lemma lem3700477 {A B : Type'} : (term410 A B) = (term401 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700476 A B f)). Qed.
Lemma lem3700478 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700479 {A B : Type'} : (term411 A B) = (term412 A B).
Proof. exact (MK_COMB (@lem3700478 A B) (@lem3700477 A B)). Qed.
Lemma lem3700480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700481 {A B : Type'} : (term413 A B) = (term414 A B).
Proof. exact (MK_COMB (@lem3700480) (@lem3700479 A B)). Qed.
Lemma lem3700482 {A B : Type'} (f : A -> B) : (term405 A B f) = (term393 A B f).
Proof. exact (eq_refl (term405 A B f)). Qed.
Lemma lem3700483 {A B : Type'} : (term415 A B) = (term402 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700482 A B f)). Qed.
Lemma lem3700484 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700485 {A B : Type'} : (term416 A B) = (term417 A B).
Proof. exact (MK_COMB (@lem3700484 A B) (@lem3700483 A B)). Qed.
Lemma lem3700486 {A B : Type'} : (term400 A B) = (term418 A B).
Proof. exact (MK_COMB (@lem3700481 A B) (@lem3700485 A B)). Qed.
Lemma lem3700487 {A B : Type'} : ((term399 A B) = (term400 A B)) = ((term396 A B) = (term418 A B)).
Proof. exact (MK_COMB (@lem3700475 A B) (@lem3700486 A B)). Qed.
Lemma lem3700488 {A B : Type'} : (term396 A B) = (term418 A B).
Proof. exact (EQ_MP (@lem3700487 A B) (@lem3700465 A B)). Qed.
Lemma lem3700677 {A B : Type'} : (term352 A B) = (term418 A B).
Proof. exact (TRANS (@lem3700461 A B) (@lem3700488 A B)). Qed.
Lemma lem3700679 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3700680 {A : Type'} (P : Prop) (Q : type686 A) : (term214 A P Q) = (term215 A P Q).
Proof. exact (@lem3700679 (A -> Prop) P Q). Qed.
Lemma lem3700681 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term419 A B s t f) = (term420 A B s t f).
Proof. exact (@lem3700680 A (term322 A B t f s) (term45 A B s t f)). Qed.
Lemma lem3700682 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term331 A B s t f s') = (term44 A B s t f s').
Proof. exact (eq_refl (term331 A B s t f s')). Qed.
Lemma lem3700683 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term421 A B s t f) = (term45 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3700682 A B s t f s')). Qed.
Lemma lem3700684 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3700685 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term422 A B s t f) = (term46 A B s t f).
Proof. exact (MK_COMB (@lem3700684 A) (@lem3700683 A B s t f)). Qed.
Lemma lem3700686 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term337 A B t f s) = (term337 A B t f s).
Proof. exact (eq_refl (term337 A B t f s)). Qed.
Lemma lem3700687 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term419 A B s t f) = (term339 A B s t f).
Proof. exact (MK_COMB (@lem3700686 A B t f s) (@lem3700685 A B s t f)). Qed.
Lemma lem3700688 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700689 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term423 A B s t f) = (term424 A B s t f).
Proof. exact (MK_COMB (@lem3700688) (@lem3700687 A B s t f)). Qed.
Lemma lem3700690 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term331 A B s t f s') = (term44 A B s t f s').
Proof. exact (eq_refl (term331 A B s t f s')). Qed.
Lemma lem3700691 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term337 A B t f s) = (term337 A B t f s).
Proof. exact (eq_refl (term337 A B t f s)). Qed.
Lemma lem3700692 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term425 A B s t f s') = (term426 A B s t f s').
Proof. exact (MK_COMB (@lem3700691 A B t f s) (@lem3700690 A B s t f s')). Qed.
Lemma lem3700693 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term427 A B s t f) = (term428 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3700692 A B s t f s')). Qed.
Lemma lem3700694 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3700695 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term420 A B s t f) = (term429 A B s t f).
Proof. exact (MK_COMB (@lem3700694 A) (@lem3700693 A B s t f)). Qed.
Lemma lem3700696 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : ((term419 A B s t f) = (term420 A B s t f)) = ((term339 A B s t f) = (term429 A B s t f)).
Proof. exact (MK_COMB (@lem3700689 A B s t f) (@lem3700695 A B s t f)). Qed.
Lemma lem3700697 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term339 A B s t f) = (term429 A B s t f).
Proof. exact (EQ_MP (@lem3700696 A B s t f) (@lem3700681 A B s t f)). Qed.
Lemma lem3700698 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term356 A B s f) = (term430 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700697 A B s t f)). Qed.
Lemma lem3700699 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700700 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term371 A B s f) = (term431 A B s f).
Proof. exact (MK_COMB (@lem3700699 B) (@lem3700698 A B s f)). Qed.
Lemma lem3700702 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3700703 {A B : Type'} (P : type841 A B) : (term432 A B P) = (term433 A B P).
Proof. exact (@lem3700702 (B -> Prop) (A -> Prop) P). Qed.
Lemma lem3700704 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term434 A B s f) = (term435 A B s f).
Proof. exact (@lem3700703 A B (term436 A B s f)). Qed.
Lemma lem3700705 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term437 A B s f t) = (term428 A B s t f).
Proof. exact (eq_refl (term437 A B s f t)). Qed.
Lemma lem3700706 {A : Type'} (s' : A -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3700707 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term438 A B s f t s') = (term439 A B s t f s').
Proof. exact (MK_COMB (@lem3700705 A B s t f) (@lem3700706 A s')). Qed.
Lemma lem3700708 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term439 A B s t f s') = (term426 A B s t f s').
Proof. exact (eq_refl (term439 A B s t f s')). Qed.
Lemma lem3700709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term438 A B s f t s') = (term426 A B s t f s').
Proof. exact (TRANS (@lem3700707 A B s t f s') (@lem3700708 A B s t f s')). Qed.
Lemma lem3700710 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term440 A B s f t) = (term428 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3700709 A B s t f s')). Qed.
Lemma lem3700711 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3700712 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term441 A B s f t) = (term429 A B s t f).
Proof. exact (MK_COMB (@lem3700711 A) (@lem3700710 A B s t f)). Qed.
Lemma lem3700713 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term442 A B s f) = (term430 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700712 A B s t f)). Qed.
Lemma lem3700714 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700715 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term434 A B s f) = (term431 A B s f).
Proof. exact (MK_COMB (@lem3700714 B) (@lem3700713 A B s f)). Qed.
Lemma lem3700716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700717 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term443 A B s f) = (term444 A B s f).
Proof. exact (MK_COMB (@lem3700716) (@lem3700715 A B s f)). Qed.
Lemma lem3700718 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term437 A B s f t) = (term428 A B s t f).
Proof. exact (eq_refl (term437 A B s f t)). Qed.
Lemma lem3700719 {A B : Type'} (s' : type860 A B) (t : B -> Prop) : (s' t) = (s' t).
Proof. exact (eq_refl (s' t)). Qed.
Lemma lem3700720 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) (t : B -> Prop) : (term445 A B s f s' t) = (term446 A B s f s' t).
Proof. exact (MK_COMB (@lem3700718 A B s t f) (@lem3700719 A B s' t)). Qed.
Lemma lem3700721 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) (t : B -> Prop) : (term446 A B s f s' t) = (term447 A B s f s' t).
Proof. exact (eq_refl (term446 A B s f s' t)). Qed.
Lemma lem3700722 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) (t : B -> Prop) : (term445 A B s f s' t) = (term447 A B s f s' t).
Proof. exact (TRANS (@lem3700720 A B s f s' t) (@lem3700721 A B s f s' t)). Qed.
Lemma lem3700723 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term448 A B s f s') = (term449 A B s f s').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700722 A B s f s' t)). Qed.
Lemma lem3700724 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700725 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term450 A B s f s') = (term451 A B s f s').
Proof. exact (MK_COMB (@lem3700724 B) (@lem3700723 A B s f s')). Qed.
Lemma lem3700726 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term452 A B s f) = (term453 A B s f).
Proof. exact (fun_ext (fun s' : type860 A B => @lem3700725 A B s f s')). Qed.
Lemma lem3700727 {A B : Type'} : (@ex ((B -> Prop) -> A -> Prop)) = (@ex ((B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700728 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term435 A B s f) = (term454 A B s f).
Proof. exact (MK_COMB (@lem3700727 A B) (@lem3700726 A B s f)). Qed.
Lemma lem3700729 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term434 A B s f) = (term435 A B s f)) = ((term431 A B s f) = (term454 A B s f)).
Proof. exact (MK_COMB (@lem3700717 A B s f) (@lem3700728 A B s f)). Qed.
Lemma lem3700730 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term431 A B s f) = (term454 A B s f).
Proof. exact (EQ_MP (@lem3700729 A B s f) (@lem3700704 A B s f)). Qed.
Lemma lem3700731 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term371 A B s f) = (term454 A B s f).
Proof. exact (TRANS (@lem3700700 A B s f) (@lem3700730 A B s f)). Qed.
Lemma lem3700732 {A B : Type'} (f : A -> B) : (term378 A B f) = (term455 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700731 A B s f)). Qed.
Lemma lem3700733 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700734 {A B : Type'} (f : A -> B) : (term393 A B f) = (term456 A B f).
Proof. exact (MK_COMB (@lem3700733 A) (@lem3700732 A B f)). Qed.
Lemma lem3700736 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3700737 {A B : Type'} (P : type607 A B) : (term457 A B P) = (term458 A B P).
Proof. exact (@lem3700736 (A -> Prop) (type860 A B) P). Qed.
Lemma lem3700738 {A B : Type'} (f : A -> B) : (term459 A B f) = (term460 A B f).
Proof. exact (@lem3700737 A B (term461 A B f)). Qed.
Lemma lem3700739 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term462 A B f s) = (term453 A B s f).
Proof. exact (eq_refl (term462 A B f s)). Qed.
Lemma lem3700740 {A B : Type'} (s' : type860 A B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3700741 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term463 A B f s s') = (term464 A B s f s').
Proof. exact (MK_COMB (@lem3700739 A B s f) (@lem3700740 A B s')). Qed.
Lemma lem3700742 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term464 A B s f s') = (term451 A B s f s').
Proof. exact (eq_refl (term464 A B s f s')). Qed.
Lemma lem3700743 {A B : Type'} (s : A -> Prop) (f : A -> B) (s' : type860 A B) : (term463 A B f s s') = (term451 A B s f s').
Proof. exact (TRANS (@lem3700741 A B s f s') (@lem3700742 A B s f s')). Qed.
Lemma lem3700744 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term465 A B f s) = (term453 A B s f).
Proof. exact (fun_ext (fun s' : type860 A B => @lem3700743 A B s f s')). Qed.
Lemma lem3700745 {A B : Type'} : (@ex ((B -> Prop) -> A -> Prop)) = (@ex ((B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700746 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term466 A B f s) = (term454 A B s f).
Proof. exact (MK_COMB (@lem3700745 A B) (@lem3700744 A B s f)). Qed.
Lemma lem3700747 {A B : Type'} (f : A -> B) : (term467 A B f) = (term455 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700746 A B s f)). Qed.
Lemma lem3700748 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700749 {A B : Type'} (f : A -> B) : (term459 A B f) = (term456 A B f).
Proof. exact (MK_COMB (@lem3700748 A) (@lem3700747 A B f)). Qed.
Lemma lem3700750 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700751 {A B : Type'} (f : A -> B) : (term468 A B f) = (term469 A B f).
Proof. exact (MK_COMB (@lem3700750) (@lem3700749 A B f)). Qed.
Lemma lem3700752 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term462 A B f s) = (term453 A B s f).
Proof. exact (eq_refl (term462 A B f s)). Qed.
Lemma lem3700753 {A B : Type'} (s' : type657 A B) (s : A -> Prop) : (s' s) = (s' s).
Proof. exact (eq_refl (s' s)). Qed.
Lemma lem3700754 {A B : Type'} (f : A -> B) (s' : type657 A B) (s : A -> Prop) : (term470 A B f s' s) = (term471 A B f s' s).
Proof. exact (MK_COMB (@lem3700752 A B s f) (@lem3700753 A B s' s)). Qed.
Lemma lem3700755 {A B : Type'} (f : A -> B) (s' : type657 A B) (s : A -> Prop) : (term471 A B f s' s) = (term472 A B f s' s).
Proof. exact (eq_refl (term471 A B f s' s)). Qed.
Lemma lem3700756 {A B : Type'} (f : A -> B) (s' : type657 A B) (s : A -> Prop) : (term470 A B f s' s) = (term472 A B f s' s).
Proof. exact (TRANS (@lem3700754 A B f s' s) (@lem3700755 A B f s' s)). Qed.
Lemma lem3700757 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term473 A B f s') = (term474 A B f s').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3700756 A B f s' s)). Qed.
Lemma lem3700758 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3700759 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term475 A B f s') = (term476 A B f s').
Proof. exact (MK_COMB (@lem3700758 A) (@lem3700757 A B f s')). Qed.
Lemma lem3700760 {A B : Type'} (f : A -> B) : (term477 A B f) = (term478 A B f).
Proof. exact (fun_ext (fun s' : type657 A B => @lem3700759 A B f s')). Qed.
Lemma lem3700761 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700762 {A B : Type'} (f : A -> B) : (term460 A B f) = (term479 A B f).
Proof. exact (MK_COMB (@lem3700761 A B) (@lem3700760 A B f)). Qed.
Lemma lem3700763 {A B : Type'} (f : A -> B) : ((term459 A B f) = (term460 A B f)) = ((term456 A B f) = (term479 A B f)).
Proof. exact (MK_COMB (@lem3700751 A B f) (@lem3700762 A B f)). Qed.
Lemma lem3700764 {A B : Type'} (f : A -> B) : (term456 A B f) = (term479 A B f).
Proof. exact (EQ_MP (@lem3700763 A B f) (@lem3700738 A B f)). Qed.
Lemma lem3700765 {A B : Type'} (f : A -> B) : (term393 A B f) = (term479 A B f).
Proof. exact (TRANS (@lem3700734 A B f) (@lem3700764 A B f)). Qed.
Lemma lem3700766 {A B : Type'} : (term402 A B) = (term480 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700765 A B f)). Qed.
Lemma lem3700767 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700768 {A B : Type'} : (term417 A B) = (term481 A B).
Proof. exact (MK_COMB (@lem3700767 A B) (@lem3700766 A B)). Qed.
Lemma lem3700770 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3700771 {A B : Type'} (P : type501 A B) : (term482 A B P) = (term483 A B P).
Proof. exact (@lem3700770 (A -> B) (type657 A B) P). Qed.
Lemma lem3700772 {A B : Type'} : (term484 A B) = (term485 A B).
Proof. exact (@lem3700771 A B (term486 A B)). Qed.
Lemma lem3700773 {A B : Type'} (f : A -> B) : (term487 A B f) = (term478 A B f).
Proof. exact (eq_refl (term487 A B f)). Qed.
Lemma lem3700774 {A B : Type'} (s' : type657 A B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3700775 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term488 A B f s') = (term489 A B f s').
Proof. exact (MK_COMB (@lem3700773 A B f) (@lem3700774 A B s')). Qed.
Lemma lem3700776 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term489 A B f s') = (term476 A B f s').
Proof. exact (eq_refl (term489 A B f s')). Qed.
Lemma lem3700777 {A B : Type'} (f : A -> B) (s' : type657 A B) : (term488 A B f s') = (term476 A B f s').
Proof. exact (TRANS (@lem3700775 A B f s') (@lem3700776 A B f s')). Qed.
Lemma lem3700778 {A B : Type'} (f : A -> B) : (term490 A B f) = (term478 A B f).
Proof. exact (fun_ext (fun s' : type657 A B => @lem3700777 A B f s')). Qed.
Lemma lem3700779 {A B : Type'} : (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700780 {A B : Type'} (f : A -> B) : (term491 A B f) = (term479 A B f).
Proof. exact (MK_COMB (@lem3700779 A B) (@lem3700778 A B f)). Qed.
Lemma lem3700781 {A B : Type'} : (term492 A B) = (term480 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3700780 A B f)). Qed.
Lemma lem3700782 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700783 {A B : Type'} : (term484 A B) = (term481 A B).
Proof. exact (MK_COMB (@lem3700782 A B) (@lem3700781 A B)). Qed.
Lemma lem3700784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700785 {A B : Type'} : (term493 A B) = (term494 A B).
Proof. exact (MK_COMB (@lem3700784) (@lem3700783 A B)). Qed.
Lemma lem3700786 {A B : Type'} (f : A -> B) : (term487 A B f) = (term478 A B f).
Proof. exact (eq_refl (term487 A B f)). Qed.
Lemma lem3700787 {A B : Type'} (s' : type525 A B) (f : A -> B) : (s' f) = (s' f).
Proof. exact (eq_refl (s' f)). Qed.
Lemma lem3700788 {A B : Type'} (s' : type525 A B) (f : A -> B) : (term495 A B s' f) = (term496 A B s' f).
Proof. exact (MK_COMB (@lem3700786 A B f) (@lem3700787 A B s' f)). Qed.
Lemma lem3700789 {A B : Type'} (s' : type525 A B) (f : A -> B) : (term496 A B s' f) = (term497 A B s' f).
Proof. exact (eq_refl (term496 A B s' f)). Qed.
Lemma lem3700790 {A B : Type'} (s' : type525 A B) (f : A -> B) : (term495 A B s' f) = (term497 A B s' f).
Proof. exact (TRANS (@lem3700788 A B s' f) (@lem3700789 A B s' f)). Qed.
Lemma lem3700791 {A B : Type'} (s' : type525 A B) : (term498 A B s') = (term499 A B s').
Proof. exact (fun_ext (fun f : A -> B => @lem3700790 A B s' f)). Qed.
Lemma lem3700792 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3700793 {A B : Type'} (s' : type525 A B) : (term500 A B s') = (term501 A B s').
Proof. exact (MK_COMB (@lem3700792 A B) (@lem3700791 A B s')). Qed.
Lemma lem3700794 {A B : Type'} : (term502 A B) = (term503 A B).
Proof. exact (fun_ext (fun s' : type525 A B => @lem3700793 A B s')). Qed.
Lemma lem3700795 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700796 {A B : Type'} : (term485 A B) = (term504 A B).
Proof. exact (MK_COMB (@lem3700795 A B) (@lem3700794 A B)). Qed.
Lemma lem3700797 {A B : Type'} : ((term484 A B) = (term485 A B)) = ((term481 A B) = (term504 A B)).
Proof. exact (MK_COMB (@lem3700785 A B) (@lem3700796 A B)). Qed.
Lemma lem3700798 {A B : Type'} : (term481 A B) = (term504 A B).
Proof. exact (EQ_MP (@lem3700797 A B) (@lem3700772 A B)). Qed.
Lemma lem3700799 {A B : Type'} : (term417 A B) = (term504 A B).
Proof. exact (TRANS (@lem3700768 A B) (@lem3700798 A B)). Qed.
Lemma lem3700800 {A B : Type'} : (term414 A B) = (term414 A B).
Proof. exact (eq_refl (term414 A B)). Qed.
Lemma lem3700801 {A B : Type'} : (term418 A B) = (term505 A B).
Proof. exact (MK_COMB (@lem3700800 A B) (@lem3700799 A B)). Qed.
Lemma lem3700803 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3700804 {A B : Type'} (P : Prop) (Q : type99 A B) : (term506 A B P Q) = (term507 A B P Q).
Proof. exact (@lem3700803 (type525 A B) P Q). Qed.
Lemma lem3700805 {A B : Type'} : (term508 A B) = (term509 A B).
Proof. exact (@lem3700804 A B (term412 A B) (term503 A B)). Qed.
Lemma lem3700806 {A B : Type'} (s' : type525 A B) : (term510 A B s') = (term501 A B s').
Proof. exact (eq_refl (term510 A B s')). Qed.
Lemma lem3700807 {A B : Type'} : (term511 A B) = (term503 A B).
Proof. exact (fun_ext (fun s' : type525 A B => @lem3700806 A B s')). Qed.
Lemma lem3700808 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700809 {A B : Type'} : (term512 A B) = (term504 A B).
Proof. exact (MK_COMB (@lem3700808 A B) (@lem3700807 A B)). Qed.
Lemma lem3700810 {A B : Type'} : (term414 A B) = (term414 A B).
Proof. exact (eq_refl (term414 A B)). Qed.
Lemma lem3700811 {A B : Type'} : (term508 A B) = (term505 A B).
Proof. exact (MK_COMB (@lem3700810 A B) (@lem3700809 A B)). Qed.
Lemma lem3700812 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700813 {A B : Type'} : (term513 A B) = (term514 A B).
Proof. exact (MK_COMB (@lem3700812) (@lem3700811 A B)). Qed.
Lemma lem3700814 {A B : Type'} (s' : type525 A B) : (term510 A B s') = (term501 A B s').
Proof. exact (eq_refl (term510 A B s')). Qed.
Lemma lem3700815 {A B : Type'} : (term414 A B) = (term414 A B).
Proof. exact (eq_refl (term414 A B)). Qed.
Lemma lem3700816 {A B : Type'} (s' : type525 A B) : (term515 A B s') = (term516 A B s').
Proof. exact (MK_COMB (@lem3700815 A B) (@lem3700814 A B s')). Qed.
Lemma lem3700817 {A B : Type'} : (term517 A B) = (term518 A B).
Proof. exact (fun_ext (fun s' : type525 A B => @lem3700816 A B s')). Qed.
Lemma lem3700818 {A B : Type'} : (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)) = (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> B) -> (A -> Prop) -> (B -> Prop) -> A -> Prop))). Qed.
Lemma lem3700819 {A B : Type'} : (term509 A B) = (term519 A B).
Proof. exact (MK_COMB (@lem3700818 A B) (@lem3700817 A B)). Qed.
Lemma lem3700820 {A B : Type'} : ((term508 A B) = (term509 A B)) = ((term505 A B) = (term519 A B)).
Proof. exact (MK_COMB (@lem3700813 A B) (@lem3700819 A B)). Qed.
Lemma lem3700821 {A B : Type'} : (term505 A B) = (term519 A B).
Proof. exact (EQ_MP (@lem3700820 A B) (@lem3700805 A B)). Qed.
Lemma lem3700822 {A B : Type'} : (term418 A B) = (term519 A B).
Proof. exact (TRANS (@lem3700801 A B) (@lem3700821 A B)). Qed.
Lemma lem3700823 {A B : Type'} : (term352 A B) = (term519 A B).
Proof. exact (TRANS (@lem3700677 A B) (@lem3700822 A B)). Qed.
Lemma lem3700824 {A B : Type'} : (term12 A B) = (term519 A B).
Proof. exact (TRANS (@lem3700040 A B) (@lem3700823 A B)). Qed.
Lemma lem3700825 {A B : Type'} (h1 : term12 A B) : term519 A B.
Proof. exact (EQ_MP (@lem3700824 A B) (@lem3698946 A B h1)). Qed.
Lemma lem3700834 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term109 B t f s) = (term110 B t f s).
Proof. exact (@lem17045 (@FINITE B t) (term111 B t f s)). Qed.
Lemma lem3700848 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term112 B s t f s') = (term113 B s t f s').
Proof. exact (@lem17045 (@SUBSET B s' s) (t = (@IMAGE B B f s'))). Qed.
Lemma lem3700853 {B : Type'} (s' : B -> Prop) : (term67 B s') = (term67 B s').
Proof. exact (eq_refl (term67 B s')). Qed.
Lemma lem3700854 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term114 B s t f s') = (term115 B s t f s').
Proof. exact (MK_COMB (@lem3700853 B s') (@lem3700848 B s t f s')). Qed.
Lemma lem3700855 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term116 B s t f s') = (term114 B s t f s').
Proof. exact (@lem17045 (@FINITE B s') (term117 B s t f s')). Qed.
Lemma lem3700856 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term116 B s t f s') = (term115 B s t f s').
Proof. exact (TRANS (@lem3700855 B s t f s') (@lem3700854 B s t f s')). Qed.
Lemma lem3700859 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term34 B s t f s') = (term34 B s t f s').
Proof. exact (eq_refl (term34 B s t f s')). Qed.
Lemma lem3700860 {B : Type'} (P : type686 B) : (term72 B P) = (term73 B P).
Proof. exact (@lem18394 (B -> Prop) P). Qed.
Lemma lem3700861 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term118 B s t f) = (term119 B s t f).
Proof. exact (@lem3700860 B (term35 B s t f)). Qed.
Lemma lem3700862 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term120 B s t f s') = (term34 B s t f s').
Proof. exact (eq_refl (term120 B s t f s')). Qed.
Lemma lem3700863 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3700864 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term121 B s t f s') = (term116 B s t f s').
Proof. exact (MK_COMB (@lem3700863) (@lem3700862 B s t f s')). Qed.
Lemma lem3700865 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term121 B s t f s') = (term115 B s t f s').
Proof. exact (TRANS (@lem3700864 B s t f s') (@lem3700856 B s t f s')). Qed.
Lemma lem3700866 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term122 B s t f) = (term123 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3700865 B s t f s')). Qed.
Lemma lem3700867 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700868 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term119 B s t f) = (term124 B s t f).
Proof. exact (MK_COMB (@lem3700867 B) (@lem3700866 B s t f)). Qed.
Lemma lem3700869 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term118 B s t f) = (term124 B s t f).
Proof. exact (TRANS (@lem3700861 B s t f) (@lem3700868 B s t f)). Qed.
Lemma lem3700870 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term35 B s t f) = (term35 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3700859 B s t f s')). Qed.
Lemma lem3700871 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3700872 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term36 B s t f) = (term36 B s t f).
Proof. exact (MK_COMB (@lem3700871 B) (@lem3700870 B s t f)). Qed.
Lemma lem3700873 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3700874 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term125 B t f s) = (term126 B t f s).
Proof. exact (MK_COMB (@lem3700873) (@lem3700834 B t f s)). Qed.
Lemma lem3700875 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term127 B s t f) = (term128 B s t f).
Proof. exact (MK_COMB (@lem3700874 B t f s) (@lem3700872 B s t f)). Qed.
Lemma lem3700877 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term129 B t f s) = (term129 B t f s).
Proof. exact (eq_refl (term129 B t f s)). Qed.
Lemma lem3700878 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term130 B s t f) = (term131 B s t f).
Proof. exact (MK_COMB (@lem3700877 B t f s) (@lem3700869 B s t f)). Qed.
Lemma lem3700879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700880 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term132 B s t f) = (term133 B s t f).
Proof. exact (MK_COMB (@lem3700879) (@lem3700878 B s t f)). Qed.
Lemma lem3700881 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term134 B s t f) = (term135 B s t f).
Proof. exact (MK_COMB (@lem3700880 B s t f) (@lem3700875 B s t f)). Qed.
Lemma lem3700882 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term38 B t f s) = (term36 B s t f)) = (term134 B s t f).
Proof. exact (@lem17784 (term38 B t f s) (term36 B s t f)). Qed.
Lemma lem3700883 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term38 B t f s) = (term36 B s t f)) = (term135 B s t f).
Proof. exact (TRANS (@lem3700882 B s t f) (@lem3700881 B s t f)). Qed.
Lemma lem3700884 {B : Type'} (s : B -> Prop) (f : B -> B) : (term39 B s f) = (term136 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700883 B s t f)). Qed.
Lemma lem3700885 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700886 {B : Type'} (s : B -> Prop) (f : B -> B) : (term40 B s f) = (term137 B s f).
Proof. exact (MK_COMB (@lem3700885 B) (@lem3700884 B s f)). Qed.
Lemma lem3700887 {B : Type'} (f : B -> B) : (term41 B f) = (term138 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3700886 B s f)). Qed.
Lemma lem3700888 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700889 {B : Type'} (f : B -> B) : (term42 B f) = (term139 B f).
Proof. exact (MK_COMB (@lem3700888 B) (@lem3700887 B f)). Qed.
Lemma lem3700890 {B : Type'} : (term43 B) = (term140 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3700889 B f)). Qed.
Lemma lem3700891 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3700892 {B : Type'} : (term13 B) = (term141 B).
Proof. exact (MK_COMB (@lem3700891 B) (@lem3700890 B)). Qed.
Lemma lem3700902 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3700903 {B : Type'} (P : type686 B) (Q : type686 B) : (term144 B P Q) = (term145 B P Q).
Proof. exact (@lem3700902 (B -> Prop) P Q). Qed.
Lemma lem3700904 {B : Type'} (s : B -> Prop) (f : B -> B) : (term146 B s f) = (term147 B s f).
Proof. exact (@lem3700903 B (term148 B s f) (term149 B s f)). Qed.
Lemma lem3700905 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term150 B s f t) = (term131 B s t f).
Proof. exact (eq_refl (term150 B s f t)). Qed.
Lemma lem3700906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700907 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term151 B s f t) = (term133 B s t f).
Proof. exact (MK_COMB (@lem3700906) (@lem3700905 B s t f)). Qed.
Lemma lem3700908 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term152 B s f t) = (term128 B s t f).
Proof. exact (eq_refl (term152 B s f t)). Qed.
Lemma lem3700909 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term153 B s f t) = (term135 B s t f).
Proof. exact (MK_COMB (@lem3700907 B s t f) (@lem3700908 B s t f)). Qed.
Lemma lem3700910 {B : Type'} (s : B -> Prop) (f : B -> B) : (term154 B s f) = (term136 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700909 B s t f)). Qed.
Lemma lem3700911 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700912 {B : Type'} (s : B -> Prop) (f : B -> B) : (term146 B s f) = (term137 B s f).
Proof. exact (MK_COMB (@lem3700911 B) (@lem3700910 B s f)). Qed.
Lemma lem3700913 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3700914 {B : Type'} (s : B -> Prop) (f : B -> B) : (term155 B s f) = (term156 B s f).
Proof. exact (MK_COMB (@lem3700913) (@lem3700912 B s f)). Qed.
Lemma lem3700915 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term150 B s f t) = (term131 B s t f).
Proof. exact (eq_refl (term150 B s f t)). Qed.
Lemma lem3700916 {B : Type'} (s : B -> Prop) (f : B -> B) : (term157 B s f) = (term148 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700915 B s t f)). Qed.
Lemma lem3700917 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700918 {B : Type'} (s : B -> Prop) (f : B -> B) : (term158 B s f) = (term159 B s f).
Proof. exact (MK_COMB (@lem3700917 B) (@lem3700916 B s f)). Qed.
Lemma lem3700919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3700920 {B : Type'} (s : B -> Prop) (f : B -> B) : (term160 B s f) = (term161 B s f).
Proof. exact (MK_COMB (@lem3700919) (@lem3700918 B s f)). Qed.
Lemma lem3700921 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term152 B s f t) = (term128 B s t f).
Proof. exact (eq_refl (term152 B s f t)). Qed.
Lemma lem3700922 {B : Type'} (s : B -> Prop) (f : B -> B) : (term162 B s f) = (term149 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3700921 B s t f)). Qed.
Lemma lem3700923 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3700924 {B : Type'} (s : B -> Prop) (f : B -> B) : (term163 B s f) = (term164 B s f).
Proof. exact (MK_COMB (@lem3700923 B) (@lem3700922 B s f)). Qed.
Lemma lem3700925 {B : Type'} (s : B -> Prop) (f : B -> B) : (term147 B s f) = (term165 B s f).
Proof. exact (MK_COMB (@lem3700920 B s f) (@lem3700924 B s f)). Qed.
Lemma lem3700926 {B : Type'} (s : B -> Prop) (f : B -> B) : ((term146 B s f) = (term147 B s f)) = ((term137 B s f) = (term165 B s f)).
Proof. exact (MK_COMB (@lem3700914 B s f) (@lem3700925 B s f)). Qed.
Lemma lem3700927 {B : Type'} (s : B -> Prop) (f : B -> B) : (term137 B s f) = (term165 B s f).
Proof. exact (EQ_MP (@lem3700926 B s f) (@lem3700904 B s f)). Qed.
Lemma lem3701100 {B : Type'} (f : B -> B) : (term138 B f) = (term166 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3700927 B s f)). Qed.
Lemma lem3701101 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701102 {B : Type'} (f : B -> B) : (term139 B f) = (term167 B f).
Proof. exact (MK_COMB (@lem3701101 B) (@lem3701100 B f)). Qed.
Lemma lem3701104 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3701105 {B : Type'} (P : type686 B) (Q : type686 B) : (term144 B P Q) = (term145 B P Q).
Proof. exact (@lem3701104 (B -> Prop) P Q). Qed.
Lemma lem3701106 {B : Type'} (f : B -> B) : (term168 B f) = (term169 B f).
Proof. exact (@lem3701105 B (term170 B f) (term171 B f)). Qed.
Lemma lem3701107 {B : Type'} (s : B -> Prop) (f : B -> B) : (term172 B f s) = (term159 B s f).
Proof. exact (eq_refl (term172 B f s)). Qed.
Lemma lem3701108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3701109 {B : Type'} (s : B -> Prop) (f : B -> B) : (term173 B f s) = (term161 B s f).
Proof. exact (MK_COMB (@lem3701108) (@lem3701107 B s f)). Qed.
Lemma lem3701110 {B : Type'} (s : B -> Prop) (f : B -> B) : (term174 B f s) = (term164 B s f).
Proof. exact (eq_refl (term174 B f s)). Qed.
Lemma lem3701111 {B : Type'} (s : B -> Prop) (f : B -> B) : (term175 B f s) = (term165 B s f).
Proof. exact (MK_COMB (@lem3701109 B s f) (@lem3701110 B s f)). Qed.
Lemma lem3701112 {B : Type'} (f : B -> B) : (term176 B f) = (term166 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701111 B s f)). Qed.
Lemma lem3701113 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701114 {B : Type'} (f : B -> B) : (term168 B f) = (term167 B f).
Proof. exact (MK_COMB (@lem3701113 B) (@lem3701112 B f)). Qed.
Lemma lem3701115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701116 {B : Type'} (f : B -> B) : (term177 B f) = (term178 B f).
Proof. exact (MK_COMB (@lem3701115) (@lem3701114 B f)). Qed.
Lemma lem3701117 {B : Type'} (s : B -> Prop) (f : B -> B) : (term172 B f s) = (term159 B s f).
Proof. exact (eq_refl (term172 B f s)). Qed.
Lemma lem3701118 {B : Type'} (f : B -> B) : (term179 B f) = (term170 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701117 B s f)). Qed.
Lemma lem3701119 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701120 {B : Type'} (f : B -> B) : (term180 B f) = (term181 B f).
Proof. exact (MK_COMB (@lem3701119 B) (@lem3701118 B f)). Qed.
Lemma lem3701121 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3701122 {B : Type'} (f : B -> B) : (term182 B f) = (term183 B f).
Proof. exact (MK_COMB (@lem3701121) (@lem3701120 B f)). Qed.
Lemma lem3701123 {B : Type'} (s : B -> Prop) (f : B -> B) : (term174 B f s) = (term164 B s f).
Proof. exact (eq_refl (term174 B f s)). Qed.
Lemma lem3701124 {B : Type'} (f : B -> B) : (term184 B f) = (term171 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701123 B s f)). Qed.
Lemma lem3701125 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701126 {B : Type'} (f : B -> B) : (term185 B f) = (term186 B f).
Proof. exact (MK_COMB (@lem3701125 B) (@lem3701124 B f)). Qed.
Lemma lem3701127 {B : Type'} (f : B -> B) : (term169 B f) = (term187 B f).
Proof. exact (MK_COMB (@lem3701122 B f) (@lem3701126 B f)). Qed.
Lemma lem3701128 {B : Type'} (f : B -> B) : ((term168 B f) = (term169 B f)) = ((term167 B f) = (term187 B f)).
Proof. exact (MK_COMB (@lem3701116 B f) (@lem3701127 B f)). Qed.
Lemma lem3701129 {B : Type'} (f : B -> B) : (term167 B f) = (term187 B f).
Proof. exact (EQ_MP (@lem3701128 B f) (@lem3701106 B f)). Qed.
Lemma lem3701310 {B : Type'} (f : B -> B) : (term139 B f) = (term187 B f).
Proof. exact (TRANS (@lem3701102 B f) (@lem3701129 B f)). Qed.
Lemma lem3701311 {B : Type'} : (term140 B) = (term188 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3701310 B f)). Qed.
Lemma lem3701312 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701313 {B : Type'} : (term141 B) = (term189 B).
Proof. exact (MK_COMB (@lem3701312 B) (@lem3701311 B)). Qed.
Lemma lem3701315 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term142 A P Q) = (term143 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3701316 {B : Type'} (P : type488 B) (Q : type488 B) : (term190 B P Q) = (term191 B P Q).
Proof. exact (@lem3701315 (B -> B) P Q). Qed.
Lemma lem3701317 {B : Type'} : (term192 B) = (term193 B).
Proof. exact (@lem3701316 B (term194 B) (term195 B)). Qed.
Lemma lem3701318 {B : Type'} (f : B -> B) : (term196 B f) = (term181 B f).
Proof. exact (eq_refl (term196 B f)). Qed.
Lemma lem3701319 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3701320 {B : Type'} (f : B -> B) : (term197 B f) = (term183 B f).
Proof. exact (MK_COMB (@lem3701319) (@lem3701318 B f)). Qed.
Lemma lem3701321 {B : Type'} (f : B -> B) : (term198 B f) = (term186 B f).
Proof. exact (eq_refl (term198 B f)). Qed.
Lemma lem3701322 {B : Type'} (f : B -> B) : (term199 B f) = (term187 B f).
Proof. exact (MK_COMB (@lem3701320 B f) (@lem3701321 B f)). Qed.
Lemma lem3701323 {B : Type'} : (term200 B) = (term188 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3701322 B f)). Qed.
Lemma lem3701324 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701325 {B : Type'} : (term192 B) = (term189 B).
Proof. exact (MK_COMB (@lem3701324 B) (@lem3701323 B)). Qed.
Lemma lem3701326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701327 {B : Type'} : (term201 B) = (term202 B).
Proof. exact (MK_COMB (@lem3701326) (@lem3701325 B)). Qed.
Lemma lem3701328 {B : Type'} (f : B -> B) : (term196 B f) = (term181 B f).
Proof. exact (eq_refl (term196 B f)). Qed.
Lemma lem3701329 {B : Type'} : (term203 B) = (term194 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3701328 B f)). Qed.
Lemma lem3701330 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701331 {B : Type'} : (term204 B) = (term205 B).
Proof. exact (MK_COMB (@lem3701330 B) (@lem3701329 B)). Qed.
Lemma lem3701332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3701333 {B : Type'} : (term206 B) = (term207 B).
Proof. exact (MK_COMB (@lem3701332) (@lem3701331 B)). Qed.
Lemma lem3701334 {B : Type'} (f : B -> B) : (term198 B f) = (term186 B f).
Proof. exact (eq_refl (term198 B f)). Qed.
Lemma lem3701335 {B : Type'} : (term208 B) = (term195 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3701334 B f)). Qed.
Lemma lem3701336 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701337 {B : Type'} : (term209 B) = (term210 B).
Proof. exact (MK_COMB (@lem3701336 B) (@lem3701335 B)). Qed.
Lemma lem3701338 {B : Type'} : (term193 B) = (term211 B).
Proof. exact (MK_COMB (@lem3701333 B) (@lem3701337 B)). Qed.
Lemma lem3701339 {B : Type'} : ((term192 B) = (term193 B)) = ((term189 B) = (term211 B)).
Proof. exact (MK_COMB (@lem3701327 B) (@lem3701338 B)). Qed.
Lemma lem3701340 {B : Type'} : (term189 B) = (term211 B).
Proof. exact (EQ_MP (@lem3701339 B) (@lem3701317 B)). Qed.
Lemma lem3701529 {B : Type'} : (term141 B) = (term211 B).
Proof. exact (TRANS (@lem3701313 B) (@lem3701340 B)). Qed.
Lemma lem3701531 {A : Type'} (P : Prop) (Q : A -> Prop) : (term212 A P Q) = (term213 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3701532 {B : Type'} (P : Prop) (Q : type686 B) : (term214 B P Q) = (term215 B P Q).
Proof. exact (@lem3701531 (B -> Prop) P Q). Qed.
Lemma lem3701533 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term216 B s t f) = (term217 B s t f).
Proof. exact (@lem3701532 B (term110 B t f s) (term35 B s t f)). Qed.
Lemma lem3701534 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term120 B s t f s') = (term34 B s t f s').
Proof. exact (eq_refl (term120 B s t f s')). Qed.
Lemma lem3701535 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term218 B s t f) = (term35 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3701534 B s t f s')). Qed.
Lemma lem3701536 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3701537 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term219 B s t f) = (term36 B s t f).
Proof. exact (MK_COMB (@lem3701536 B) (@lem3701535 B s t f)). Qed.
Lemma lem3701538 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term126 B t f s) = (term126 B t f s).
Proof. exact (eq_refl (term126 B t f s)). Qed.
Lemma lem3701539 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term216 B s t f) = (term128 B s t f).
Proof. exact (MK_COMB (@lem3701538 B t f s) (@lem3701537 B s t f)). Qed.
Lemma lem3701540 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701541 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term220 B s t f) = (term221 B s t f).
Proof. exact (MK_COMB (@lem3701540) (@lem3701539 B s t f)). Qed.
Lemma lem3701542 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term120 B s t f s') = (term34 B s t f s').
Proof. exact (eq_refl (term120 B s t f s')). Qed.
Lemma lem3701543 {B : Type'} (t : B -> Prop) (f : B -> B) (s : B -> Prop) : (term126 B t f s) = (term126 B t f s).
Proof. exact (eq_refl (term126 B t f s)). Qed.
Lemma lem3701544 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term222 B s t f s') = (term223 B s t f s').
Proof. exact (MK_COMB (@lem3701543 B t f s) (@lem3701542 B s t f s')). Qed.
Lemma lem3701545 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term224 B s t f) = (term225 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3701544 B s t f s')). Qed.
Lemma lem3701546 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3701547 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term217 B s t f) = (term226 B s t f).
Proof. exact (MK_COMB (@lem3701546 B) (@lem3701545 B s t f)). Qed.
Lemma lem3701548 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : ((term216 B s t f) = (term217 B s t f)) = ((term128 B s t f) = (term226 B s t f)).
Proof. exact (MK_COMB (@lem3701541 B s t f) (@lem3701547 B s t f)). Qed.
Lemma lem3701549 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term128 B s t f) = (term226 B s t f).
Proof. exact (EQ_MP (@lem3701548 B s t f) (@lem3701533 B s t f)). Qed.
Lemma lem3701550 {B : Type'} (s : B -> Prop) (f : B -> B) : (term149 B s f) = (term227 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3701549 B s t f)). Qed.
Lemma lem3701551 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701552 {B : Type'} (s : B -> Prop) (f : B -> B) : (term164 B s f) = (term228 B s f).
Proof. exact (MK_COMB (@lem3701551 B) (@lem3701550 B s f)). Qed.
Lemma lem3701554 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3701555 {B : Type'} (P : type639 B) : (term231 B P) = (term232 B P).
Proof. exact (@lem3701554 (B -> Prop) (B -> Prop) P). Qed.
Lemma lem3701556 {B : Type'} (s : B -> Prop) (f : B -> B) : (term233 B s f) = (term234 B s f).
Proof. exact (@lem3701555 B (term235 B s f)). Qed.
Lemma lem3701557 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term236 B s f t) = (term225 B s t f).
Proof. exact (eq_refl (term236 B s f t)). Qed.
Lemma lem3701558 {B : Type'} (s' : B -> Prop) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3701559 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term237 B s f t s') = (term238 B s t f s').
Proof. exact (MK_COMB (@lem3701557 B s t f) (@lem3701558 B s')). Qed.
Lemma lem3701560 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term238 B s t f s') = (term223 B s t f s').
Proof. exact (eq_refl (term238 B s t f s')). Qed.
Lemma lem3701561 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) (s' : B -> Prop) : (term237 B s f t s') = (term223 B s t f s').
Proof. exact (TRANS (@lem3701559 B s t f s') (@lem3701560 B s t f s')). Qed.
Lemma lem3701562 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term239 B s f t) = (term225 B s t f).
Proof. exact (fun_ext (fun s' : B -> Prop => @lem3701561 B s t f s')). Qed.
Lemma lem3701563 {B : Type'} : (@ex (B -> Prop)) = (@ex (B -> Prop)).
Proof. exact (eq_refl (@ex (B -> Prop))). Qed.
Lemma lem3701564 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term240 B s f t) = (term226 B s t f).
Proof. exact (MK_COMB (@lem3701563 B) (@lem3701562 B s t f)). Qed.
Lemma lem3701565 {B : Type'} (s : B -> Prop) (f : B -> B) : (term241 B s f) = (term227 B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3701564 B s t f)). Qed.
Lemma lem3701566 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701567 {B : Type'} (s : B -> Prop) (f : B -> B) : (term233 B s f) = (term228 B s f).
Proof. exact (MK_COMB (@lem3701566 B) (@lem3701565 B s f)). Qed.
Lemma lem3701568 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701569 {B : Type'} (s : B -> Prop) (f : B -> B) : (term242 B s f) = (term243 B s f).
Proof. exact (MK_COMB (@lem3701568) (@lem3701567 B s f)). Qed.
Lemma lem3701570 {B : Type'} (s : B -> Prop) (t : B -> Prop) (f : B -> B) : (term236 B s f t) = (term225 B s t f).
Proof. exact (eq_refl (term236 B s f t)). Qed.
Lemma lem3701571 {B : Type'} (s' : type672 B) (t : B -> Prop) : (s' t) = (s' t).
Proof. exact (eq_refl (s' t)). Qed.
Lemma lem3701572 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) (t : B -> Prop) : (term244 B s f s' t) = (term245 B s f s' t).
Proof. exact (MK_COMB (@lem3701570 B s t f) (@lem3701571 B s' t)). Qed.
Lemma lem3701573 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) (t : B -> Prop) : (term245 B s f s' t) = (term246 B s f s' t).
Proof. exact (eq_refl (term245 B s f s' t)). Qed.
Lemma lem3701574 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) (t : B -> Prop) : (term244 B s f s' t) = (term246 B s f s' t).
Proof. exact (TRANS (@lem3701572 B s f s' t) (@lem3701573 B s f s' t)). Qed.
Lemma lem3701575 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term247 B s f s') = (term248 B s f s').
Proof. exact (fun_ext (fun t : B -> Prop => @lem3701574 B s f s' t)). Qed.
Lemma lem3701576 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701577 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term249 B s f s') = (term250 B s f s').
Proof. exact (MK_COMB (@lem3701576 B) (@lem3701575 B s f s')). Qed.
Lemma lem3701578 {B : Type'} (s : B -> Prop) (f : B -> B) : (term251 B s f) = (term252 B s f).
Proof. exact (fun_ext (fun s' : type672 B => @lem3701577 B s f s')). Qed.
Lemma lem3701579 {B : Type'} : (@ex ((B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701580 {B : Type'} (s : B -> Prop) (f : B -> B) : (term234 B s f) = (term253 B s f).
Proof. exact (MK_COMB (@lem3701579 B) (@lem3701578 B s f)). Qed.
Lemma lem3701581 {B : Type'} (s : B -> Prop) (f : B -> B) : ((term233 B s f) = (term234 B s f)) = ((term228 B s f) = (term253 B s f)).
Proof. exact (MK_COMB (@lem3701569 B s f) (@lem3701580 B s f)). Qed.
Lemma lem3701582 {B : Type'} (s : B -> Prop) (f : B -> B) : (term228 B s f) = (term253 B s f).
Proof. exact (EQ_MP (@lem3701581 B s f) (@lem3701556 B s f)). Qed.
Lemma lem3701583 {B : Type'} (s : B -> Prop) (f : B -> B) : (term164 B s f) = (term253 B s f).
Proof. exact (TRANS (@lem3701552 B s f) (@lem3701582 B s f)). Qed.
Lemma lem3701584 {B : Type'} (f : B -> B) : (term171 B f) = (term254 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701583 B s f)). Qed.
Lemma lem3701585 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701586 {B : Type'} (f : B -> B) : (term186 B f) = (term255 B f).
Proof. exact (MK_COMB (@lem3701585 B) (@lem3701584 B f)). Qed.
Lemma lem3701588 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3701589 {B : Type'} (P : type596 B) : (term256 B P) = (term257 B P).
Proof. exact (@lem3701588 (B -> Prop) (type672 B) P). Qed.
Lemma lem3701590 {B : Type'} (f : B -> B) : (term258 B f) = (term259 B f).
Proof. exact (@lem3701589 B (term260 B f)). Qed.
Lemma lem3701591 {B : Type'} (s : B -> Prop) (f : B -> B) : (term261 B f s) = (term252 B s f).
Proof. exact (eq_refl (term261 B f s)). Qed.
Lemma lem3701592 {B : Type'} (s' : type672 B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3701593 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term262 B f s s') = (term263 B s f s').
Proof. exact (MK_COMB (@lem3701591 B s f) (@lem3701592 B s')). Qed.
Lemma lem3701594 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term263 B s f s') = (term250 B s f s').
Proof. exact (eq_refl (term263 B s f s')). Qed.
Lemma lem3701595 {B : Type'} (s : B -> Prop) (f : B -> B) (s' : type672 B) : (term262 B f s s') = (term250 B s f s').
Proof. exact (TRANS (@lem3701593 B s f s') (@lem3701594 B s f s')). Qed.
Lemma lem3701596 {B : Type'} (s : B -> Prop) (f : B -> B) : (term264 B f s) = (term252 B s f).
Proof. exact (fun_ext (fun s' : type672 B => @lem3701595 B s f s')). Qed.
Lemma lem3701597 {B : Type'} : (@ex ((B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701598 {B : Type'} (s : B -> Prop) (f : B -> B) : (term265 B f s) = (term253 B s f).
Proof. exact (MK_COMB (@lem3701597 B) (@lem3701596 B s f)). Qed.
Lemma lem3701599 {B : Type'} (f : B -> B) : (term266 B f) = (term254 B f).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701598 B s f)). Qed.
Lemma lem3701600 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701601 {B : Type'} (f : B -> B) : (term258 B f) = (term255 B f).
Proof. exact (MK_COMB (@lem3701600 B) (@lem3701599 B f)). Qed.
Lemma lem3701602 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701603 {B : Type'} (f : B -> B) : (term267 B f) = (term268 B f).
Proof. exact (MK_COMB (@lem3701602) (@lem3701601 B f)). Qed.
Lemma lem3701604 {B : Type'} (s : B -> Prop) (f : B -> B) : (term261 B f s) = (term252 B s f).
Proof. exact (eq_refl (term261 B f s)). Qed.
Lemma lem3701605 {B : Type'} (s' : type636 B) (s : B -> Prop) : (s' s) = (s' s).
Proof. exact (eq_refl (s' s)). Qed.
Lemma lem3701606 {B : Type'} (f : B -> B) (s' : type636 B) (s : B -> Prop) : (term269 B f s' s) = (term270 B f s' s).
Proof. exact (MK_COMB (@lem3701604 B s f) (@lem3701605 B s' s)). Qed.
Lemma lem3701607 {B : Type'} (f : B -> B) (s' : type636 B) (s : B -> Prop) : (term270 B f s' s) = (term271 B f s' s).
Proof. exact (eq_refl (term270 B f s' s)). Qed.
Lemma lem3701608 {B : Type'} (f : B -> B) (s' : type636 B) (s : B -> Prop) : (term269 B f s' s) = (term271 B f s' s).
Proof. exact (TRANS (@lem3701606 B f s' s) (@lem3701607 B f s' s)). Qed.
Lemma lem3701609 {B : Type'} (f : B -> B) (s' : type636 B) : (term272 B f s') = (term273 B f s').
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701608 B f s' s)). Qed.
Lemma lem3701610 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701611 {B : Type'} (f : B -> B) (s' : type636 B) : (term274 B f s') = (term275 B f s').
Proof. exact (MK_COMB (@lem3701610 B) (@lem3701609 B f s')). Qed.
Lemma lem3701612 {B : Type'} (f : B -> B) : (term276 B f) = (term277 B f).
Proof. exact (fun_ext (fun s' : type636 B => @lem3701611 B f s')). Qed.
Lemma lem3701613 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701614 {B : Type'} (f : B -> B) : (term259 B f) = (term278 B f).
Proof. exact (MK_COMB (@lem3701613 B) (@lem3701612 B f)). Qed.
Lemma lem3701615 {B : Type'} (f : B -> B) : ((term258 B f) = (term259 B f)) = ((term255 B f) = (term278 B f)).
Proof. exact (MK_COMB (@lem3701603 B f) (@lem3701614 B f)). Qed.
Lemma lem3701616 {B : Type'} (f : B -> B) : (term255 B f) = (term278 B f).
Proof. exact (EQ_MP (@lem3701615 B f) (@lem3701590 B f)). Qed.
Lemma lem3701617 {B : Type'} (f : B -> B) : (term186 B f) = (term278 B f).
Proof. exact (TRANS (@lem3701586 B f) (@lem3701616 B f)). Qed.
Lemma lem3701618 {B : Type'} : (term195 B) = (term279 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3701617 B f)). Qed.
Lemma lem3701619 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701620 {B : Type'} : (term210 B) = (term280 B).
Proof. exact (MK_COMB (@lem3701619 B) (@lem3701618 B)). Qed.
Lemma lem3701622 {A B : Type'} (P : type1413 A B) : (term229 A B P) = (term230 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3701623 {B : Type'} (P : type480 B) : (term281 B P) = (term282 B P).
Proof. exact (@lem3701622 (B -> B) (type636 B) P). Qed.
Lemma lem3701624 {B : Type'} : (term283 B) = (term284 B).
Proof. exact (@lem3701623 B (term285 B)). Qed.
Lemma lem3701625 {B : Type'} (f : B -> B) : (term286 B f) = (term277 B f).
Proof. exact (eq_refl (term286 B f)). Qed.
Lemma lem3701626 {B : Type'} (s' : type636 B) : s' = s'.
Proof. exact (eq_refl s'). Qed.
Lemma lem3701627 {B : Type'} (f : B -> B) (s' : type636 B) : (term287 B f s') = (term288 B f s').
Proof. exact (MK_COMB (@lem3701625 B f) (@lem3701626 B s')). Qed.
Lemma lem3701628 {B : Type'} (f : B -> B) (s' : type636 B) : (term288 B f s') = (term275 B f s').
Proof. exact (eq_refl (term288 B f s')). Qed.
Lemma lem3701629 {B : Type'} (f : B -> B) (s' : type636 B) : (term287 B f s') = (term275 B f s').
Proof. exact (TRANS (@lem3701627 B f s') (@lem3701628 B f s')). Qed.
Lemma lem3701630 {B : Type'} (f : B -> B) : (term289 B f) = (term277 B f).
Proof. exact (fun_ext (fun s' : type636 B => @lem3701629 B f s')). Qed.
Lemma lem3701631 {B : Type'} : (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701632 {B : Type'} (f : B -> B) : (term290 B f) = (term278 B f).
Proof. exact (MK_COMB (@lem3701631 B) (@lem3701630 B f)). Qed.
Lemma lem3701633 {B : Type'} : (term291 B) = (term279 B).
Proof. exact (fun_ext (fun f : B -> B => @lem3701632 B f)). Qed.
Lemma lem3701634 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701635 {B : Type'} : (term283 B) = (term280 B).
Proof. exact (MK_COMB (@lem3701634 B) (@lem3701633 B)). Qed.
Lemma lem3701636 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701637 {B : Type'} : (term292 B) = (term293 B).
Proof. exact (MK_COMB (@lem3701636) (@lem3701635 B)). Qed.
Lemma lem3701638 {B : Type'} (f : B -> B) : (term286 B f) = (term277 B f).
Proof. exact (eq_refl (term286 B f)). Qed.
Lemma lem3701639 {B : Type'} (s' : type483 B) (f : B -> B) : (s' f) = (s' f).
Proof. exact (eq_refl (s' f)). Qed.
Lemma lem3701640 {B : Type'} (s' : type483 B) (f : B -> B) : (term294 B s' f) = (term295 B s' f).
Proof. exact (MK_COMB (@lem3701638 B f) (@lem3701639 B s' f)). Qed.
Lemma lem3701641 {B : Type'} (s' : type483 B) (f : B -> B) : (term295 B s' f) = (term296 B s' f).
Proof. exact (eq_refl (term295 B s' f)). Qed.
Lemma lem3701642 {B : Type'} (s' : type483 B) (f : B -> B) : (term294 B s' f) = (term296 B s' f).
Proof. exact (TRANS (@lem3701640 B s' f) (@lem3701641 B s' f)). Qed.
Lemma lem3701643 {B : Type'} (s' : type483 B) : (term297 B s') = (term298 B s').
Proof. exact (fun_ext (fun f : B -> B => @lem3701642 B s' f)). Qed.
Lemma lem3701644 {B : Type'} : (@all (B -> B)) = (@all (B -> B)).
Proof. exact (eq_refl (@all (B -> B))). Qed.
Lemma lem3701645 {B : Type'} (s' : type483 B) : (term299 B s') = (term300 B s').
Proof. exact (MK_COMB (@lem3701644 B) (@lem3701643 B s')). Qed.
Lemma lem3701646 {B : Type'} : (term301 B) = (term302 B).
Proof. exact (fun_ext (fun s' : type483 B => @lem3701645 B s')). Qed.
Lemma lem3701647 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701648 {B : Type'} : (term284 B) = (term303 B).
Proof. exact (MK_COMB (@lem3701647 B) (@lem3701646 B)). Qed.
Lemma lem3701649 {B : Type'} : ((term283 B) = (term284 B)) = ((term280 B) = (term303 B)).
Proof. exact (MK_COMB (@lem3701637 B) (@lem3701648 B)). Qed.
Lemma lem3701650 {B : Type'} : (term280 B) = (term303 B).
Proof. exact (EQ_MP (@lem3701649 B) (@lem3701624 B)). Qed.
Lemma lem3701651 {B : Type'} : (term210 B) = (term303 B).
Proof. exact (TRANS (@lem3701620 B) (@lem3701650 B)). Qed.
Lemma lem3701652 {B : Type'} : (term207 B) = (term207 B).
Proof. exact (eq_refl (term207 B)). Qed.
Lemma lem3701653 {B : Type'} : (term211 B) = (term304 B).
Proof. exact (MK_COMB (@lem3701652 B) (@lem3701651 B)). Qed.
Lemma lem3701655 {A : Type'} (P : Prop) (Q : A -> Prop) : (term305 A P Q) = (term306 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3701656 {B : Type'} (P : Prop) (Q : type92 B) : (term307 B P Q) = (term308 B P Q).
Proof. exact (@lem3701655 (type483 B) P Q). Qed.
Lemma lem3701657 {B : Type'} : (term309 B) = (term310 B).
Proof. exact (@lem3701656 B (term205 B) (term302 B)). Qed.
Lemma lem3701658 {B : Type'} (s' : type483 B) : (term311 B s') = (term300 B s').
Proof. exact (eq_refl (term311 B s')). Qed.
Lemma lem3701659 {B : Type'} : (term312 B) = (term302 B).
Proof. exact (fun_ext (fun s' : type483 B => @lem3701658 B s')). Qed.
Lemma lem3701660 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701661 {B : Type'} : (term313 B) = (term303 B).
Proof. exact (MK_COMB (@lem3701660 B) (@lem3701659 B)). Qed.
Lemma lem3701662 {B : Type'} : (term207 B) = (term207 B).
Proof. exact (eq_refl (term207 B)). Qed.
Lemma lem3701663 {B : Type'} : (term309 B) = (term304 B).
Proof. exact (MK_COMB (@lem3701662 B) (@lem3701661 B)). Qed.
Lemma lem3701664 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3701665 {B : Type'} : (term314 B) = (term315 B).
Proof. exact (MK_COMB (@lem3701664) (@lem3701663 B)). Qed.
Lemma lem3701666 {B : Type'} (s' : type483 B) : (term311 B s') = (term300 B s').
Proof. exact (eq_refl (term311 B s')). Qed.
Lemma lem3701667 {B : Type'} : (term207 B) = (term207 B).
Proof. exact (eq_refl (term207 B)). Qed.
Lemma lem3701668 {B : Type'} (s' : type483 B) : (term316 B s') = (term317 B s').
Proof. exact (MK_COMB (@lem3701667 B) (@lem3701666 B s')). Qed.
Lemma lem3701669 {B : Type'} : (term318 B) = (term319 B).
Proof. exact (fun_ext (fun s' : type483 B => @lem3701668 B s')). Qed.
Lemma lem3701670 {B : Type'} : (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)) = (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop)).
Proof. exact (eq_refl (@ex ((B -> B) -> (B -> Prop) -> (B -> Prop) -> B -> Prop))). Qed.
Lemma lem3701671 {B : Type'} : (term310 B) = (term320 B).
Proof. exact (MK_COMB (@lem3701670 B) (@lem3701669 B)). Qed.
Lemma lem3701672 {B : Type'} : ((term309 B) = (term310 B)) = ((term304 B) = (term320 B)).
Proof. exact (MK_COMB (@lem3701665 B) (@lem3701671 B)). Qed.
Lemma lem3701673 {B : Type'} : (term304 B) = (term320 B).
Proof. exact (EQ_MP (@lem3701672 B) (@lem3701657 B)). Qed.
Lemma lem3701674 {B : Type'} : (term211 B) = (term320 B).
Proof. exact (TRANS (@lem3701653 B) (@lem3701673 B)). Qed.
Lemma lem3701675 {B : Type'} : (term141 B) = (term320 B).
Proof. exact (TRANS (@lem3701529 B) (@lem3701674 B)). Qed.
Lemma lem3701676 {B : Type'} : (term13 B) = (term320 B).
Proof. exact (TRANS (@lem3700892 B) (@lem3701675 B)). Qed.
Lemma lem3701677 {B : Type'} (h1 : term13 B) : term320 B.
Proof. exact (EQ_MP (@lem3701676 B) (@lem3698947 B h1)). Qed.
Lemma lem3701691 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3701692 {B : Type'} : (term33 B) = (term33 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701691 B s)). Qed.
Lemma lem3701693 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701702 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (MK_COMB (@lem3701693 B) (@lem3701692 B)). Qed.
Lemma lem3701703 {B : Type'} (h1 : term11 B) : term11 B.
Proof. exact (EQ_MP (@lem3701702 B) (@lem3698949 B h1)). Qed.
Lemma lem3701705 {A B : Type'} (s'' : type525 A B) (h1 : term516 A B s'') : term516 A B s''.
Proof. exact (h1). Qed.
Lemma lem3701707 {A B : Type'} (f : A -> B) (h1 : term100 A B f) : term100 A B f.
Proof. exact (h1). Qed.
Lemma lem3701708 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term93 A B s f) : term93 A B s f.
Proof. exact (h1). Qed.
Lemma lem3701709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term83 A B s t f.
Proof. exact (h1). Qed.
Lemma lem3701723 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3701724 {B : Type'} : (term33 B) = (term33 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3701723 B s)). Qed.
Lemma lem3701725 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701726 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (MK_COMB (@lem3701725 B) (@lem3701724 B)). Qed.
Lemma lem3701727 {B : Type'} (h1 : term11 B) : term11 B.
Proof. exact (EQ_MP (@lem3701726 B) (@lem3701703 B h1)). Qed.
Lemma lem3701925 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term520 A B s'' f s t) = (term520 A B s'' f s t).
Proof. exact (eq_refl (term520 A B s'' f s t)). Qed.
Lemma lem3701926 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term521 A B s'' f s) = (term521 A B s'' f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3701925 A B s'' f s t)). Qed.
Lemma lem3701927 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701928 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term522 A B s'' f s) = (term522 A B s'' f s).
Proof. exact (MK_COMB (@lem3701927 B) (@lem3701926 A B s'' f s)). Qed.
Lemma lem3701929 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term523 A B s'' f) = (term523 A B s'' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3701928 A B s'' f s)). Qed.
Lemma lem3701930 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3701931 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term497 A B s'' f) = (term497 A B s'' f).
Proof. exact (MK_COMB (@lem3701930 A) (@lem3701929 A B s'' f)). Qed.
Lemma lem3701932 {A B : Type'} (s'' : type525 A B) : (term499 A B s'') = (term499 A B s'').
Proof. exact (fun_ext (fun f : A -> B => @lem3701931 A B s'' f)). Qed.
Lemma lem3701933 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3701934 {A B : Type'} (s'' : type525 A B) : (term501 A B s'') = (term501 A B s'').
Proof. exact (MK_COMB (@lem3701933 A B) (@lem3701932 A B s'')). Qed.
Lemma lem3701963 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term326 A B s t f s') = (term326 A B s t f s').
Proof. exact (eq_refl (term326 A B s t f s')). Qed.
Lemma lem3701964 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term334 A B s t f) = (term334 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3701963 A B s t f s')). Qed.
Lemma lem3701965 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3701966 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term335 A B s t f) = (term335 A B s t f).
Proof. exact (MK_COMB (@lem3701965 A) (@lem3701964 A B s t f)). Qed.
Lemma lem3701983 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term340 A B t f s) = (term340 A B t f s).
Proof. exact (eq_refl (term340 A B t f s)). Qed.
Lemma lem3701984 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term342 A B s t f) = (term342 A B s t f).
Proof. exact (MK_COMB (@lem3701983 A B t f s) (@lem3701966 A B s t f)). Qed.
Lemma lem3701985 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term355 A B s f) = (term355 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3701984 A B s t f)). Qed.
Lemma lem3701986 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3701987 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term366 A B s f) = (term366 A B s f).
Proof. exact (MK_COMB (@lem3701986 B) (@lem3701985 A B s f)). Qed.
Lemma lem3701988 {A B : Type'} (f : A -> B) : (term377 A B f) = (term377 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3701987 A B s f)). Qed.
Lemma lem3701989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3701990 {A B : Type'} (f : A -> B) : (term388 A B f) = (term388 A B f).
Proof. exact (MK_COMB (@lem3701989 A) (@lem3701988 A B f)). Qed.
Lemma lem3701991 {A B : Type'} : (term401 A B) = (term401 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem3701990 A B f)). Qed.
Lemma lem3701992 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3701993 {A B : Type'} : (term412 A B) = (term412 A B).
Proof. exact (MK_COMB (@lem3701992 A B) (@lem3701991 A B)). Qed.
Lemma lem3701994 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3701995 {A B : Type'} : (term414 A B) = (term414 A B).
Proof. exact (MK_COMB (@lem3701994) (@lem3701993 A B)). Qed.
Lemma lem3701996 {A B : Type'} (s'' : type525 A B) : (term516 A B s'') = (term516 A B s'').
Proof. exact (MK_COMB (@lem3701995 A B) (@lem3701934 A B s'')). Qed.
Lemma lem3701997 {A B : Type'} (s'' : type525 A B) (h1 : term516 A B s'') : term516 A B s''.
Proof. exact (EQ_MP (@lem3701996 A B s'') (@lem3701705 A B s'' h1)). Qed.
Lemma lem3702161 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term69 A B s t f s') = (term69 A B s t f s').
Proof. exact (eq_refl (term69 A B s t f s')). Qed.
Lemma lem3702162 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term79 A B s t f) = (term79 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3702161 A B s t f s')). Qed.
Lemma lem3702163 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3702164 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term80 A B s t f) = (term80 A B s t f).
Proof. exact (MK_COMB (@lem3702163 A) (@lem3702162 A B s t f)). Qed.
Lemma lem3702181 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term81 A B t f s) = (term81 A B t f s).
Proof. exact (eq_refl (term81 A B t f s)). Qed.
Lemma lem3702182 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term83 A B s t f) = (term83 A B s t f).
Proof. exact (MK_COMB (@lem3702181 A B t f s) (@lem3702164 A B s t f)). Qed.
Lemma lem3702183 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term83 A B s t f.
Proof. exact (EQ_MP (@lem3702182 A B s t f) (@lem3701709 A B s t f h1)). Qed.
Lemma lem3702184 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term80 A B s t f.
Proof. exact (proj2 (@lem3702183 A B s t f h1)). Qed.
Lemma lem3702185 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term48 A B t f s.
Proof. exact (proj1 (@lem3702183 A B s t f h1)). Qed.
Lemma lem3702190 {A B : Type'} (s'' : type525 A B) (h1 : term516 A B s'') : term501 A B s''.
Proof. exact (proj2 (@lem3701997 A B s'' h1)). Qed.
Lemma lem3702202 {B : Type'} (s : B -> Prop) : (@SUBSET B s s) = (@SUBSET B s s).
Proof. exact (eq_refl (@SUBSET B s s)). Qed.
Lemma lem3702203 {B : Type'} : (term33 B) = (term33 B).
Proof. exact (fun_ext (fun s : B -> Prop => @lem3702202 B s)). Qed.
Lemma lem3702204 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3702206 {B : Type'} : (term11 B) = (term11 B).
Proof. exact (MK_COMB (@lem3702204 B) (@lem3702203 B)). Qed.
Lemma lem3702207 {B : Type'} (h1 : term11 B) : term11 B.
Proof. exact (EQ_MP (@lem3702206 B) (@lem3701727 B h1)). Qed.
Lemma lem3702221 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (s' : A -> Prop) : (term69 A B s t f s') = (term69 A B s t f s').
Proof. exact (eq_refl (term69 A B s t f s')). Qed.
Lemma lem3702222 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term79 A B s t f) = (term79 A B s t f).
Proof. exact (fun_ext (fun s' : A -> Prop => @lem3702221 A B s t f s')). Qed.
Lemma lem3702223 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3702225 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) : (term80 A B s t f) = (term80 A B s t f).
Proof. exact (MK_COMB (@lem3702223 A) (@lem3702222 A B s t f)). Qed.
Lemma lem3702226 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term80 A B s t f.
Proof. exact (EQ_MP (@lem3702225 A B s t f) (@lem3702184 A B s t f h1)). Qed.
Lemma lem3702444 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term520 A B s'' f s t) = (term524 A B s'' f s t).
Proof. exact (@lem19490 (term525 A B s'' f s t) (term322 A B t f s) (term526 A B s'' f s t)). Qed.
Lemma lem3702451 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term527 A B s'' f s t) = (term528 A B s'' f s t).
Proof. exact (@lem19490 (term529 A B s'' f t s) (term322 A B t f s) (t = (term530 A B s'' f s t))). Qed.
Lemma lem3702454 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term531 A B s'' f s t) = (term531 A B s'' f s t).
Proof. exact (eq_refl (term531 A B s'' f s t)). Qed.
Lemma lem3702455 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term524 A B s'' f s t) = (term532 A B s'' f s t).
Proof. exact (MK_COMB (@lem3702454 A B s'' f s t) (@lem3702451 A B s'' f s t)). Qed.
Lemma lem3702457 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term520 A B s'' f s t) = (term532 A B s'' f s t).
Proof. exact (TRANS (@lem3702444 A B s'' f s t) (@lem3702455 A B s'' f s t)). Qed.
Lemma lem3702458 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term521 A B s'' f s) = (term533 A B s'' f s).
Proof. exact (fun_ext (fun t : B -> Prop => @lem3702457 A B s'' f s t)). Qed.
Lemma lem3702459 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem3702460 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) : (term522 A B s'' f s) = (term534 A B s'' f s).
Proof. exact (MK_COMB (@lem3702459 B) (@lem3702458 A B s'' f s)). Qed.
Lemma lem3702461 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term523 A B s'' f) = (term535 A B s'' f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3702460 A B s'' f s)). Qed.
Lemma lem3702462 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3702463 {A B : Type'} (s'' : type525 A B) (f : A -> B) : (term497 A B s'' f) = (term536 A B s'' f).
Proof. exact (MK_COMB (@lem3702462 A) (@lem3702461 A B s'' f)). Qed.
Lemma lem3702464 {A B : Type'} (s'' : type525 A B) : (term499 A B s'') = (term537 A B s'').
Proof. exact (fun_ext (fun f : A -> B => @lem3702463 A B s'' f)). Qed.
Lemma lem3702465 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem3702467 {A B : Type'} (s'' : type525 A B) : (term501 A B s'') = (term538 A B s'').
Proof. exact (MK_COMB (@lem3702465 A B) (@lem3702464 A B s'')). Qed.
Lemma lem3702468 {A B : Type'} (s'' : type525 A B) (h1 : term516 A B s'') : term538 A B s''.
Proof. exact (EQ_MP (@lem3702467 A B s'') (@lem3702190 A B s'' h1)). Qed.
Lemma lem3702589 {B : Type'} (_42611 : B -> Prop) (h1 : term11 B) : term539 B _42611.
Proof. exact (@lem3702207 B h1 _42611). Qed.
Lemma lem3702590 {B : Type'} (_42611 : B -> Prop) : (term539 B _42611) = (@SUBSET B _42611 _42611).
Proof. exact (eq_refl (term539 B _42611)). Qed.
Lemma lem3702592 {A B : Type'} (_42612 : A -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term540 A B s t f _42612.
Proof. exact (@lem3702226 A B s t f h1 _42612). Qed.
Lemma lem3702593 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term540 A B s t f _42612) = (term69 A B s t f _42612).
Proof. exact (eq_refl (term540 A B s t f _42612)). Qed.
Lemma lem3702628 {A B : Type'} (_42624 : A -> B) (s'' : type525 A B) (h1 : term516 A B s'') : term541 A B s'' _42624.
Proof. exact (@lem3702468 A B s'' h1 _42624). Qed.
Lemma lem3702629 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) : (term541 A B s'' _42624) = (term536 A B s'' _42624).
Proof. exact (eq_refl (term541 A B s'' _42624)). Qed.
Lemma lem3702630 {A B : Type'} (_42624 : A -> B) (s'' : type525 A B) (h1 : term516 A B s'') : term536 A B s'' _42624.
Proof. exact (EQ_MP (@lem3702629 A B s'' _42624) (@lem3702628 A B _42624 s'' h1)). Qed.
Lemma lem3702631 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term542 A B s'' _42624 _42625.
Proof. exact (@lem3702630 A B _42624 s'' h1 _42625). Qed.
Lemma lem3702632 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) : (term542 A B s'' _42624 _42625) = (term534 A B s'' _42624 _42625).
Proof. exact (eq_refl (term542 A B s'' _42624 _42625)). Qed.
Lemma lem3702633 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term534 A B s'' _42624 _42625.
Proof. exact (EQ_MP (@lem3702632 A B s'' _42624 _42625) (@lem3702631 A B _42624 _42625 s'' h1)). Qed.
Lemma lem3702634 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term543 A B s'' _42624 _42625 _42626.
Proof. exact (@lem3702633 A B _42624 _42625 s'' h1 _42626). Qed.
Lemma lem3702635 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term543 A B s'' _42624 _42625 _42626) = (term532 A B s'' _42624 _42625 _42626).
Proof. exact (eq_refl (term543 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3702636 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term532 A B s'' _42624 _42625 _42626.
Proof. exact (EQ_MP (@lem3702635 A B s'' _42624 _42625 _42626) (@lem3702634 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702664 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term528 A B s'' _42624 _42625 _42626.
Proof. exact (proj2 (@lem3702636 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702665 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term544 A B s'' _42624 _42625 _42626.
Proof. exact (proj1 (@lem3702636 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702666 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term545 A B s'' _42624 _42625 _42626.
Proof. exact (proj2 (@lem3702664 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702667 {A B : Type'} (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term546 A B s'' _42624 _42626 _42625.
Proof. exact (proj1 (@lem3702664 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702689 {A B : Type'} (_42612 : A -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term69 A B s t f _42612.
Proof. exact (EQ_MP (@lem3702593 A B s t f _42612) (@lem3702592 A B _42612 s t f h1)). Qed.
Lemma lem3702768 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term544 A B s'' _42624 _42625 _42626) = (term547 A B s'' _42624 _42625 _42626).
Proof. exact (@lem3698389 (term548 B _42626) (term549 A B _42626 _42624 _42625) (term525 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3702769 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term547 A B s'' _42624 _42625 _42626.
Proof. exact (EQ_MP (@lem3702768 A B s'' _42624 _42625 _42626) (@lem3702665 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702780 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) : (term546 A B s'' _42624 _42626 _42625) = (term550 A B s'' _42624 _42626 _42625).
Proof. exact (@lem3698389 (term548 B _42626) (term549 A B _42626 _42624 _42625) (term529 A B s'' _42624 _42626 _42625)). Qed.
Lemma lem3702781 {A B : Type'} (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term550 A B s'' _42624 _42626 _42625.
Proof. exact (EQ_MP (@lem3702780 A B s'' _42624 _42626 _42625) (@lem3702667 A B _42624 _42626 _42625 s'' h1)). Qed.
Lemma lem3702792 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term545 A B s'' _42624 _42625 _42626) = (term551 A B s'' _42624 _42625 _42626).
Proof. exact (@lem3698389 (term548 B _42626) (term549 A B _42626 _42624 _42625) (_42626 = (term530 A B s'' _42624 _42625 _42626))). Qed.
Lemma lem3702793 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term551 A B s'' _42624 _42625 _42626.
Proof. exact (EQ_MP (@lem3702792 A B s'' _42624 _42625 _42626) (@lem3702666 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3702910 {B : Type'} : (@SUBSET B) = (@SUBSET B).
Proof. exact (eq_refl (@SUBSET B)). Qed.
Lemma lem3702911 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) (h1 : _42638 = _42640) : _42638 = _42640.
Proof. exact (h1). Qed.
Lemma lem3702912 {B : Type'} (_42639 : B -> Prop) (_42641 : B -> Prop) (h1 : _42639 = _42641) : _42639 = _42641.
Proof. exact (h1). Qed.
Lemma lem3702913 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) (h1 : _42638 = _42640) : (@SUBSET B _42638) = (@SUBSET B _42640).
Proof. exact (MK_COMB (@lem3702910 B) (@lem3702911 B _42638 _42640 h1)). Qed.
Lemma lem3702914 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) (_42639 : B -> Prop) (_42641 : B -> Prop) (h1 : _42638 = _42640) (h2 : _42639 = _42641) : (@SUBSET B _42638 _42639) = (@SUBSET B _42640 _42641).
Proof. exact (MK_COMB (@lem3702913 B _42638 _42640 h1) (@lem3702912 B _42639 _42641 h2)). Qed.
Lemma lem3702916 (b : Prop) (a : Prop) : term552 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3702917 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : term553 B _42640 _42641 _42638 _42639.
Proof. exact (@lem3702916 (@SUBSET B _42640 _42641) (@SUBSET B _42638 _42639)). Qed.
Lemma lem3702918 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) (_42639 : B -> Prop) (_42641 : B -> Prop) (h1 : _42638 = _42640) (h2 : _42639 = _42641) : term554 B _42640 _42641 _42638 _42639.
Proof. exact (@lem3702917 B _42640 _42641 _42638 _42639 (@lem3702914 B _42638 _42640 _42639 _42641 h1 h2)). Qed.
Lemma lem3702919 {B : Type'} (_42641 : B -> Prop) (_42639 : B -> Prop) (_42638 : B -> Prop) (_42640 : B -> Prop) (h1 : _42638 = _42640) : term555 B _42640 _42641 _42638 _42639.
Proof. exact (fun h0 : _42639 = _42641 => @lem3702918 B _42638 _42640 _42639 _42641 h1 h0). Qed.
Lemma lem3702921 (a : Prop) (b : Prop) : (a -> b) = (term556 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3702922 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term555 B _42640 _42641 _42638 _42639) = (term557 B _42640 _42641 _42638 _42639).
Proof. exact (@lem3702921 (_42639 = _42641) (term554 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3702923 {B : Type'} (_42641 : B -> Prop) (_42639 : B -> Prop) (_42638 : B -> Prop) (_42640 : B -> Prop) (h1 : _42638 = _42640) : term557 B _42640 _42641 _42638 _42639.
Proof. exact (EQ_MP (@lem3702922 B _42640 _42641 _42638 _42639) (@lem3702919 B _42641 _42639 _42638 _42640 h1)). Qed.
Lemma lem3702924 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : term558 B _42640 _42641 _42638 _42639.
Proof. exact (fun h0 : _42638 = _42640 => @lem3702923 B _42641 _42639 _42638 _42640 h0). Qed.
Lemma lem3702926 (a : Prop) (b : Prop) : (a -> b) = (term556 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3702927 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term558 B _42640 _42641 _42638 _42639) = (term559 B _42640 _42641 _42638 _42639).
Proof. exact (@lem3702926 (_42638 = _42640) (term557 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3702928 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : term559 B _42640 _42641 _42638 _42639.
Proof. exact (EQ_MP (@lem3702927 B _42640 _42641 _42638 _42639) (@lem3702924 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : @FINITE B t.
Proof. exact (proj1 (@lem3702185 A B s t f h1)). Qed.
Lemma lem3703071 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term560 B t.
Proof. exact (fun h0 : term548 B t => @lem3703070 A B s t f h1). Qed.
Lemma lem3703073 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703074 {B : Type'} (t : B -> Prop) : (term560 B t) = (@FINITE B t).
Proof. exact (@lem3703073 (@FINITE B t)). Qed.
Lemma lem3703075 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : @FINITE B t.
Proof. exact (EQ_MP (@lem3703074 B t) (@lem3703071 A B s t f h1)). Qed.
Lemma lem3703077 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term66 A B t f s.
Proof. exact (proj2 (@lem3702185 A B s t f h1)). Qed.
Lemma lem3703078 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term562 A B t f s.
Proof. exact (fun h0 : term549 A B t f s => @lem3703077 A B s t f h1). Qed.
Lemma lem3703080 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703081 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term562 A B t f s) = (term66 A B t f s).
Proof. exact (@lem3703080 (term66 A B t f s)). Qed.
Lemma lem3703082 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term66 A B t f s.
Proof. exact (EQ_MP (@lem3703081 A B t f s) (@lem3703078 A B s t f h1)). Qed.
Lemma lem3703098 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3703099 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term563 A B s'' _42624 _42625 _42626) = (term564 A B s'' _42626 _42624 _42625).
Proof. exact (@lem3703098 (term525 A B s'' _42624 _42625 _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703105 {B : Type'} (_42626 : B -> Prop) : (term67 B _42626) = (term67 B _42626).
Proof. exact (eq_refl (term67 B _42626)). Qed.
Lemma lem3703106 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term547 A B s'' _42624 _42625 _42626) = (term565 A B s'' _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703105 B _42626) (@lem3703099 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703110 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3703111 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term565 A B s'' _42626 _42624 _42625) = (term566 A B s'' _42626 _42624 _42625).
Proof. exact (@lem3703110 (term525 A B s'' _42624 _42625 _42626) (term548 B _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703127 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term547 A B s'' _42624 _42625 _42626) = (term566 A B s'' _42626 _42624 _42625).
Proof. exact (TRANS (@lem3703106 A B s'' _42626 _42624 _42625) (@lem3703111 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703128 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3703129 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term567 A B s'' _42624 _42625 _42626) = (term568 A B s'' _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703128) (@lem3703127 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703145 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term566 A B s'' _42626 _42624 _42625) = (term566 A B s'' _42626 _42624 _42625).
Proof. exact (eq_refl (term566 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703146 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term547 A B s'' _42624 _42625 _42626) = (term566 A B s'' _42626 _42624 _42625)) = ((term566 A B s'' _42626 _42624 _42625) = (term566 A B s'' _42626 _42624 _42625)).
Proof. exact (MK_COMB (@lem3703129 A B s'' _42626 _42624 _42625) (@lem3703145 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703148 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3703149 (x : Prop) : (x = x) = True.
Proof. exact (@lem3703148 Prop x). Qed.
Lemma lem3703150 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term566 A B s'' _42626 _42624 _42625) = (term566 A B s'' _42626 _42624 _42625)) = True.
Proof. exact (@lem3703149 (term566 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703151 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term547 A B s'' _42624 _42625 _42626) = (term566 A B s'' _42626 _42624 _42625)) = True.
Proof. exact (TRANS (@lem3703146 A B s'' _42626 _42624 _42625) (@lem3703150 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703152 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : True = ((term547 A B s'' _42624 _42625 _42626) = (term566 A B s'' _42626 _42624 _42625)).
Proof. exact (SYM (@lem3703151 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703153 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term547 A B s'' _42624 _42625 _42626) = (term566 A B s'' _42626 _42624 _42625).
Proof. exact (EQ_MP (@lem3703152 A B s'' _42626 _42624 _42625) (@lem0)). Qed.
Lemma lem3703154 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term566 A B s'' _42626 _42624 _42625.
Proof. exact (EQ_MP (@lem3703153 A B s'' _42626 _42624 _42625) (@lem3702769 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3703156 (b : Prop) (a : Prop) : (a \/ b) = (term569 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3703157 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term566 A B s'' _42626 _42624 _42625) = (term570 A B s'' _42624 _42625 _42626).
Proof. exact (@lem3703156 (term322 A B _42626 _42624 _42625) (term525 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3703159 (a : Prop) (b : Prop) : (term571 a b) = (term572 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3703160 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term573 A B _42626 _42624 _42625) = (term574 A B _42626 _42624 _42625).
Proof. exact (@lem3703159 (term548 B _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703162 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703163 {B : Type'} (_42626 : B -> Prop) : (term576 B _42626) = (@FINITE B _42626).
Proof. exact (@lem3703162 (@FINITE B _42626)). Qed.
Lemma lem3703164 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3703165 {B : Type'} (_42626 : B -> Prop) : (term577 B _42626) = (term578 B _42626).
Proof. exact (MK_COMB (@lem3703164) (@lem3703163 B _42626)). Qed.
Lemma lem3703167 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703168 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term579 A B _42626 _42624 _42625) = (term66 A B _42626 _42624 _42625).
Proof. exact (@lem3703167 (term66 A B _42626 _42624 _42625)). Qed.
Lemma lem3703169 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term574 A B _42626 _42624 _42625) = (term48 A B _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703165 B _42626) (@lem3703168 A B _42626 _42624 _42625)). Qed.
Lemma lem3703170 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term573 A B _42626 _42624 _42625) = (term48 A B _42626 _42624 _42625).
Proof. exact (TRANS (@lem3703160 A B _42626 _42624 _42625) (@lem3703169 A B _42626 _42624 _42625)). Qed.
Lemma lem3703171 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3703172 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term580 A B _42626 _42624 _42625) = (term57 A B _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703171) (@lem3703170 A B _42626 _42624 _42625)). Qed.
Lemma lem3703173 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term525 A B s'' _42624 _42625 _42626) = (term525 A B s'' _42624 _42625 _42626).
Proof. exact (eq_refl (term525 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3703174 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term570 A B s'' _42624 _42625 _42626) = (term581 A B s'' _42624 _42625 _42626).
Proof. exact (MK_COMB (@lem3703172 A B _42626 _42624 _42625) (@lem3703173 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3703175 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term566 A B s'' _42626 _42624 _42625) = (term581 A B s'' _42624 _42625 _42626).
Proof. exact (TRANS (@lem3703157 A B s'' _42624 _42625 _42626) (@lem3703174 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3703177 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term48 A B t f s.
Proof. exact (conj (@lem3703075 A B s t f h1) (@lem3703082 A B s t f h1)). Qed.
Lemma lem3703179 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term581 A B s'' _42624 _42625 _42626.
Proof. exact (EQ_MP (@lem3703175 A B s'' _42624 _42625 _42626) (@lem3703154 A B _42626 _42624 _42625 s'' h1)). Qed.
Lemma lem3703180 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term581 A B s'' _42624 _42625 _42626.
Proof. exact (@lem3703179 A B _42624 _42625 _42626 s'' h1). Qed.
Lemma lem3703181 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term581 A B s'' f s t.
Proof. exact (@lem3703180 A B f s t s'' h1). Qed.
Lemma lem3703184 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term525 A B s'' f s t.
Proof. exact (@lem3703181 A B f s t s'' h1 (@lem3703177 A B s t f h2)). Qed.
Lemma lem3703185 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term582 A B s'' f s t.
Proof. exact (fun h0 : term583 A B s'' f s t => @lem3703184 A B s'' s t f h1 h2). Qed.
Lemma lem3703187 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703188 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term582 A B s'' f s t) = (term525 A B s'' f s t).
Proof. exact (@lem3703187 (term525 A B s'' f s t)). Qed.
Lemma lem3703189 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term525 A B s'' f s t.
Proof. exact (EQ_MP (@lem3703188 A B s'' f s t) (@lem3703185 A B s'' s t f h1 h2)). Qed.
Lemma lem3703191 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : @FINITE B t.
Proof. exact (proj1 (@lem3702185 A B s t f h1)). Qed.
Lemma lem3703192 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term560 B t.
Proof. exact (fun h0 : term548 B t => @lem3703191 A B s t f h1). Qed.
Lemma lem3703194 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703195 {B : Type'} (t : B -> Prop) : (term560 B t) = (@FINITE B t).
Proof. exact (@lem3703194 (@FINITE B t)). Qed.
Lemma lem3703196 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : @FINITE B t.
Proof. exact (EQ_MP (@lem3703195 B t) (@lem3703192 A B s t f h1)). Qed.
Lemma lem3703198 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term66 A B t f s.
Proof. exact (proj2 (@lem3702185 A B s t f h1)). Qed.
Lemma lem3703199 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term562 A B t f s.
Proof. exact (fun h0 : term549 A B t f s => @lem3703198 A B s t f h1). Qed.
Lemma lem3703201 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703202 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term562 A B t f s) = (term66 A B t f s).
Proof. exact (@lem3703201 (term66 A B t f s)). Qed.
Lemma lem3703203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term66 A B t f s.
Proof. exact (EQ_MP (@lem3703202 A B t f s) (@lem3703199 A B s t f h1)). Qed.
Lemma lem3703219 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3703220 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term584 A B s'' _42624 _42626 _42625) = (term585 A B s'' _42626 _42624 _42625).
Proof. exact (@lem3703219 (term529 A B s'' _42624 _42626 _42625) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703226 {B : Type'} (_42626 : B -> Prop) : (term67 B _42626) = (term67 B _42626).
Proof. exact (eq_refl (term67 B _42626)). Qed.
Lemma lem3703227 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term550 A B s'' _42624 _42626 _42625) = (term586 A B s'' _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703226 B _42626) (@lem3703220 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703231 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3703232 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term586 A B s'' _42626 _42624 _42625) = (term587 A B s'' _42626 _42624 _42625).
Proof. exact (@lem3703231 (term529 A B s'' _42624 _42626 _42625) (term548 B _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703248 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term550 A B s'' _42624 _42626 _42625) = (term587 A B s'' _42626 _42624 _42625).
Proof. exact (TRANS (@lem3703227 A B s'' _42626 _42624 _42625) (@lem3703232 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3703250 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term588 A B s'' _42624 _42626 _42625) = (term589 A B s'' _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703249) (@lem3703248 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703266 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term587 A B s'' _42626 _42624 _42625) = (term587 A B s'' _42626 _42624 _42625).
Proof. exact (eq_refl (term587 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703267 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term550 A B s'' _42624 _42626 _42625) = (term587 A B s'' _42626 _42624 _42625)) = ((term587 A B s'' _42626 _42624 _42625) = (term587 A B s'' _42626 _42624 _42625)).
Proof. exact (MK_COMB (@lem3703250 A B s'' _42626 _42624 _42625) (@lem3703266 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703269 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3703270 (x : Prop) : (x = x) = True.
Proof. exact (@lem3703269 Prop x). Qed.
Lemma lem3703271 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term587 A B s'' _42626 _42624 _42625) = (term587 A B s'' _42626 _42624 _42625)) = True.
Proof. exact (@lem3703270 (term587 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703272 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term550 A B s'' _42624 _42626 _42625) = (term587 A B s'' _42626 _42624 _42625)) = True.
Proof. exact (TRANS (@lem3703267 A B s'' _42626 _42624 _42625) (@lem3703271 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703273 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : True = ((term550 A B s'' _42624 _42626 _42625) = (term587 A B s'' _42626 _42624 _42625)).
Proof. exact (SYM (@lem3703272 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703274 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term550 A B s'' _42624 _42626 _42625) = (term587 A B s'' _42626 _42624 _42625).
Proof. exact (EQ_MP (@lem3703273 A B s'' _42626 _42624 _42625) (@lem0)). Qed.
Lemma lem3703275 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term587 A B s'' _42626 _42624 _42625.
Proof. exact (EQ_MP (@lem3703274 A B s'' _42626 _42624 _42625) (@lem3702781 A B _42624 _42626 _42625 s'' h1)). Qed.
Lemma lem3703277 (b : Prop) (a : Prop) : (a \/ b) = (term569 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3703278 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) : (term587 A B s'' _42626 _42624 _42625) = (term590 A B s'' _42624 _42626 _42625).
Proof. exact (@lem3703277 (term322 A B _42626 _42624 _42625) (term529 A B s'' _42624 _42626 _42625)). Qed.
Lemma lem3703280 (a : Prop) (b : Prop) : (term571 a b) = (term572 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3703281 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term573 A B _42626 _42624 _42625) = (term574 A B _42626 _42624 _42625).
Proof. exact (@lem3703280 (term548 B _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703283 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703284 {B : Type'} (_42626 : B -> Prop) : (term576 B _42626) = (@FINITE B _42626).
Proof. exact (@lem3703283 (@FINITE B _42626)). Qed.
Lemma lem3703285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3703286 {B : Type'} (_42626 : B -> Prop) : (term577 B _42626) = (term578 B _42626).
Proof. exact (MK_COMB (@lem3703285) (@lem3703284 B _42626)). Qed.
Lemma lem3703288 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703289 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term579 A B _42626 _42624 _42625) = (term66 A B _42626 _42624 _42625).
Proof. exact (@lem3703288 (term66 A B _42626 _42624 _42625)). Qed.
Lemma lem3703290 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term574 A B _42626 _42624 _42625) = (term48 A B _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703286 B _42626) (@lem3703289 A B _42626 _42624 _42625)). Qed.
Lemma lem3703291 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term573 A B _42626 _42624 _42625) = (term48 A B _42626 _42624 _42625).
Proof. exact (TRANS (@lem3703281 A B _42626 _42624 _42625) (@lem3703290 A B _42626 _42624 _42625)). Qed.
Lemma lem3703292 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3703293 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term580 A B _42626 _42624 _42625) = (term57 A B _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703292) (@lem3703291 A B _42626 _42624 _42625)). Qed.
Lemma lem3703294 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) : (term529 A B s'' _42624 _42626 _42625) = (term529 A B s'' _42624 _42626 _42625).
Proof. exact (eq_refl (term529 A B s'' _42624 _42626 _42625)). Qed.
Lemma lem3703295 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) : (term590 A B s'' _42624 _42626 _42625) = (term591 A B s'' _42624 _42626 _42625).
Proof. exact (MK_COMB (@lem3703293 A B _42626 _42624 _42625) (@lem3703294 A B s'' _42624 _42626 _42625)). Qed.
Lemma lem3703296 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) : (term587 A B s'' _42626 _42624 _42625) = (term591 A B s'' _42624 _42626 _42625).
Proof. exact (TRANS (@lem3703278 A B s'' _42624 _42626 _42625) (@lem3703295 A B s'' _42624 _42626 _42625)). Qed.
Lemma lem3703298 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term48 A B t f s.
Proof. exact (conj (@lem3703196 A B s t f h1) (@lem3703203 A B s t f h1)). Qed.
Lemma lem3703300 {A B : Type'} (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term591 A B s'' _42624 _42626 _42625.
Proof. exact (EQ_MP (@lem3703296 A B s'' _42624 _42626 _42625) (@lem3703275 A B _42626 _42624 _42625 s'' h1)). Qed.
Lemma lem3703301 {A B : Type'} (_42624 : A -> B) (_42626 : B -> Prop) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term591 A B s'' _42624 _42626 _42625.
Proof. exact (@lem3703300 A B _42624 _42626 _42625 s'' h1). Qed.
Lemma lem3703302 {A B : Type'} (f : A -> B) (t : B -> Prop) (s : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term591 A B s'' f t s.
Proof. exact (@lem3703301 A B f t s s'' h1). Qed.
Lemma lem3703305 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term529 A B s'' f t s.
Proof. exact (@lem3703302 A B f t s s'' h1 (@lem3703298 A B s t f h2)). Qed.
Lemma lem3703306 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term592 A B s'' f t s.
Proof. exact (fun h0 : term593 A B s'' f t s => @lem3703305 A B s'' s t f h1 h2). Qed.
Lemma lem3703308 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703309 {A B : Type'} (s'' : type525 A B) (f : A -> B) (t : B -> Prop) (s : A -> Prop) : (term592 A B s'' f t s) = (term529 A B s'' f t s).
Proof. exact (@lem3703308 (term529 A B s'' f t s)). Qed.
Lemma lem3703310 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term529 A B s'' f t s.
Proof. exact (EQ_MP (@lem3703309 A B s'' f t s) (@lem3703306 A B s'' s t f h1 h2)). Qed.
Lemma lem3703312 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem21386 (B -> Prop) x). Qed.
Lemma lem3703313 {B : Type'} (x : B -> Prop) : x = x.
Proof. exact (@lem3703312 B x). Qed.
Lemma lem3703314 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (@lem3703313 B t). Qed.
Lemma lem3703315 {B : Type'} (t : B -> Prop) : term594 B t.
Proof. exact (fun h0 : term595 B t => @lem3703314 B t). Qed.
Lemma lem3703317 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703318 {B : Type'} (t : B -> Prop) : (term594 B t) = (t = t).
Proof. exact (@lem3703317 (t = t)). Qed.
Lemma lem3703319 {B : Type'} (t : B -> Prop) : t = t.
Proof. exact (EQ_MP (@lem3703318 B t) (@lem3703315 B t)). Qed.
Lemma lem3703321 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : @FINITE B t.
Proof. exact (proj1 (@lem3702185 A B s t f h1)). Qed.
Lemma lem3703322 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term560 B t.
Proof. exact (fun h0 : term548 B t => @lem3703321 A B s t f h1). Qed.
Lemma lem3703324 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703325 {B : Type'} (t : B -> Prop) : (term560 B t) = (@FINITE B t).
Proof. exact (@lem3703324 (@FINITE B t)). Qed.
Lemma lem3703326 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : @FINITE B t.
Proof. exact (EQ_MP (@lem3703325 B t) (@lem3703322 A B s t f h1)). Qed.
Lemma lem3703328 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term66 A B t f s.
Proof. exact (proj2 (@lem3702185 A B s t f h1)). Qed.
Lemma lem3703329 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term562 A B t f s.
Proof. exact (fun h0 : term549 A B t f s => @lem3703328 A B s t f h1). Qed.
Lemma lem3703331 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703332 {A B : Type'} (t : B -> Prop) (f : A -> B) (s : A -> Prop) : (term562 A B t f s) = (term66 A B t f s).
Proof. exact (@lem3703331 (term66 A B t f s)). Qed.
Lemma lem3703333 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term66 A B t f s.
Proof. exact (EQ_MP (@lem3703332 A B t f s) (@lem3703329 A B s t f h1)). Qed.
Lemma lem3703349 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3703350 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term596 A B s'' _42624 _42625 _42626) = (term597 A B s'' _42626 _42624 _42625).
Proof. exact (@lem3703349 (_42626 = (term530 A B s'' _42624 _42625 _42626)) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703358 {B : Type'} (_42626 : B -> Prop) : (term67 B _42626) = (term67 B _42626).
Proof. exact (eq_refl (term67 B _42626)). Qed.
Lemma lem3703359 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term551 A B s'' _42624 _42625 _42626) = (term598 A B s'' _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703358 B _42626) (@lem3703350 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703363 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3703364 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term598 A B s'' _42626 _42624 _42625) = (term599 A B s'' _42626 _42624 _42625).
Proof. exact (@lem3703363 (_42626 = (term530 A B s'' _42624 _42625 _42626)) (term548 B _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703382 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term551 A B s'' _42624 _42625 _42626) = (term599 A B s'' _42626 _42624 _42625).
Proof. exact (TRANS (@lem3703359 A B s'' _42626 _42624 _42625) (@lem3703364 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703383 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3703384 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term600 A B s'' _42624 _42625 _42626) = (term601 A B s'' _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703383) (@lem3703382 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703402 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term599 A B s'' _42626 _42624 _42625) = (term599 A B s'' _42626 _42624 _42625).
Proof. exact (eq_refl (term599 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703403 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term551 A B s'' _42624 _42625 _42626) = (term599 A B s'' _42626 _42624 _42625)) = ((term599 A B s'' _42626 _42624 _42625) = (term599 A B s'' _42626 _42624 _42625)).
Proof. exact (MK_COMB (@lem3703384 A B s'' _42626 _42624 _42625) (@lem3703402 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703405 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3703406 (x : Prop) : (x = x) = True.
Proof. exact (@lem3703405 Prop x). Qed.
Lemma lem3703407 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term599 A B s'' _42626 _42624 _42625) = (term599 A B s'' _42626 _42624 _42625)) = True.
Proof. exact (@lem3703406 (term599 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703408 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : ((term551 A B s'' _42624 _42625 _42626) = (term599 A B s'' _42626 _42624 _42625)) = True.
Proof. exact (TRANS (@lem3703403 A B s'' _42626 _42624 _42625) (@lem3703407 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703409 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : True = ((term551 A B s'' _42624 _42625 _42626) = (term599 A B s'' _42626 _42624 _42625)).
Proof. exact (SYM (@lem3703408 A B s'' _42626 _42624 _42625)). Qed.
Lemma lem3703410 {A B : Type'} (s'' : type525 A B) (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term551 A B s'' _42624 _42625 _42626) = (term599 A B s'' _42626 _42624 _42625).
Proof. exact (EQ_MP (@lem3703409 A B s'' _42626 _42624 _42625) (@lem0)). Qed.
Lemma lem3703411 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term599 A B s'' _42626 _42624 _42625.
Proof. exact (EQ_MP (@lem3703410 A B s'' _42626 _42624 _42625) (@lem3702793 A B _42624 _42625 _42626 s'' h1)). Qed.
Lemma lem3703413 (b : Prop) (a : Prop) : (a \/ b) = (term569 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3703414 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term599 A B s'' _42626 _42624 _42625) = (term602 A B s'' _42624 _42625 _42626).
Proof. exact (@lem3703413 (term322 A B _42626 _42624 _42625) (_42626 = (term530 A B s'' _42624 _42625 _42626))). Qed.
Lemma lem3703416 (a : Prop) (b : Prop) : (term571 a b) = (term572 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3703417 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term573 A B _42626 _42624 _42625) = (term574 A B _42626 _42624 _42625).
Proof. exact (@lem3703416 (term548 B _42626) (term549 A B _42626 _42624 _42625)). Qed.
Lemma lem3703419 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703420 {B : Type'} (_42626 : B -> Prop) : (term576 B _42626) = (@FINITE B _42626).
Proof. exact (@lem3703419 (@FINITE B _42626)). Qed.
Lemma lem3703421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3703422 {B : Type'} (_42626 : B -> Prop) : (term577 B _42626) = (term578 B _42626).
Proof. exact (MK_COMB (@lem3703421) (@lem3703420 B _42626)). Qed.
Lemma lem3703424 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703425 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term579 A B _42626 _42624 _42625) = (term66 A B _42626 _42624 _42625).
Proof. exact (@lem3703424 (term66 A B _42626 _42624 _42625)). Qed.
Lemma lem3703426 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term574 A B _42626 _42624 _42625) = (term48 A B _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703422 B _42626) (@lem3703425 A B _42626 _42624 _42625)). Qed.
Lemma lem3703427 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term573 A B _42626 _42624 _42625) = (term48 A B _42626 _42624 _42625).
Proof. exact (TRANS (@lem3703417 A B _42626 _42624 _42625) (@lem3703426 A B _42626 _42624 _42625)). Qed.
Lemma lem3703428 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3703429 {A B : Type'} (_42626 : B -> Prop) (_42624 : A -> B) (_42625 : A -> Prop) : (term580 A B _42626 _42624 _42625) = (term57 A B _42626 _42624 _42625).
Proof. exact (MK_COMB (@lem3703428) (@lem3703427 A B _42626 _42624 _42625)). Qed.
Lemma lem3703430 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (_42626 = (term530 A B s'' _42624 _42625 _42626)) = (_42626 = (term530 A B s'' _42624 _42625 _42626)).
Proof. exact (eq_refl (_42626 = (term530 A B s'' _42624 _42625 _42626))). Qed.
Lemma lem3703431 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term602 A B s'' _42624 _42625 _42626) = (term603 A B s'' _42624 _42625 _42626).
Proof. exact (MK_COMB (@lem3703429 A B _42626 _42624 _42625) (@lem3703430 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3703432 {A B : Type'} (s'' : type525 A B) (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) : (term599 A B s'' _42626 _42624 _42625) = (term603 A B s'' _42624 _42625 _42626).
Proof. exact (TRANS (@lem3703414 A B s'' _42624 _42625 _42626) (@lem3703431 A B s'' _42624 _42625 _42626)). Qed.
Lemma lem3703434 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term48 A B t f s.
Proof. exact (conj (@lem3703326 A B s t f h1) (@lem3703333 A B s t f h1)). Qed.
Lemma lem3703436 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term603 A B s'' _42624 _42625 _42626.
Proof. exact (EQ_MP (@lem3703432 A B s'' _42624 _42625 _42626) (@lem3703411 A B _42626 _42624 _42625 s'' h1)). Qed.
Lemma lem3703437 {A B : Type'} (_42624 : A -> B) (_42625 : A -> Prop) (_42626 : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term603 A B s'' _42624 _42625 _42626.
Proof. exact (@lem3703436 A B _42624 _42625 _42626 s'' h1). Qed.
Lemma lem3703438 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (s'' : type525 A B) (h1 : term516 A B s'') : term603 A B s'' f s t.
Proof. exact (@lem3703437 A B f s t s'' h1). Qed.
Lemma lem3703441 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : t = (term530 A B s'' f s t).
Proof. exact (@lem3703438 A B f s t s'' h1 (@lem3703434 A B s t f h2)). Qed.
Lemma lem3703442 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : term604 A B s'' f s t.
Proof. exact (fun h0 : term605 A B s'' f s t => @lem3703441 A B s'' s t f h1 h2). Qed.
Lemma lem3703444 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703445 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term604 A B s'' f s t) = (t = (term530 A B s'' f s t)).
Proof. exact (@lem3703444 (t = (term530 A B s'' f s t))). Qed.
Lemma lem3703446 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term516 A B s'') (h2 : term83 A B s t f) : t = (term530 A B s'' f s t).
Proof. exact (EQ_MP (@lem3703445 A B s'' f s t) (@lem3703442 A B s'' s t f h1 h2)). Qed.
Lemma lem3703448 {B : Type'} (_42611 : B -> Prop) (h1 : term11 B) : @SUBSET B _42611 _42611.
Proof. exact (EQ_MP (@lem3702590 B _42611) (@lem3702589 B _42611 h1)). Qed.
Lemma lem3703449 {B : Type'} (_42611 : B -> Prop) (h1 : term11 B) : @SUBSET B _42611 _42611.
Proof. exact (@lem3703448 B _42611 h1). Qed.
Lemma lem3703450 {B : Type'} (t : B -> Prop) (h1 : term11 B) : @SUBSET B t t.
Proof. exact (@lem3703449 B t h1). Qed.
Lemma lem3703451 {B : Type'} (t : B -> Prop) (h1 : term11 B) : term606 B t.
Proof. exact (fun h0 : term607 B t => @lem3703450 B t h1). Qed.
Lemma lem3703453 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703454 {B : Type'} (t : B -> Prop) : (term606 B t) = (@SUBSET B t t).
Proof. exact (@lem3703453 (@SUBSET B t t)). Qed.
Lemma lem3703455 {B : Type'} (t : B -> Prop) (h1 : term11 B) : @SUBSET B t t.
Proof. exact (EQ_MP (@lem3703454 B t) (@lem3703451 B t h1)). Qed.
Lemma lem3703473 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3703474 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term557 B _42640 _42641 _42638 _42639) = (term608 B _42640 _42641 _42638 _42639).
Proof. exact (@lem3703473 (@SUBSET B _42640 _42641) (term609 B _42639 _42641) (term610 B _42638 _42639)). Qed.
Lemma lem3703492 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) : (term611 B _42638 _42640) = (term611 B _42638 _42640).
Proof. exact (eq_refl (term611 B _42638 _42640)). Qed.
Lemma lem3703493 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term559 B _42640 _42641 _42638 _42639) = (term612 B _42640 _42641 _42638 _42639).
Proof. exact (MK_COMB (@lem3703492 B _42638 _42640) (@lem3703474 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703497 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3703498 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term612 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639).
Proof. exact (@lem3703497 (@SUBSET B _42640 _42641) (term609 B _42638 _42640) (term614 B _42641 _42638 _42639)). Qed.
Lemma lem3703528 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term559 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639).
Proof. exact (TRANS (@lem3703493 B _42640 _42641 _42638 _42639) (@lem3703498 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703529 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3703530 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term615 B _42640 _42641 _42638 _42639) = (term616 B _42640 _42641 _42638 _42639).
Proof. exact (MK_COMB (@lem3703529) (@lem3703528 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703560 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term613 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639).
Proof. exact (eq_refl (term613 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703561 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : ((term559 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639)) = ((term613 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639)).
Proof. exact (MK_COMB (@lem3703530 B _42640 _42641 _42638 _42639) (@lem3703560 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703563 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3703564 (x : Prop) : (x = x) = True.
Proof. exact (@lem3703563 Prop x). Qed.
Lemma lem3703565 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : ((term613 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639)) = True.
Proof. exact (@lem3703564 (term613 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703566 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : ((term559 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639)) = True.
Proof. exact (TRANS (@lem3703561 B _42640 _42641 _42638 _42639) (@lem3703565 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703567 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : True = ((term559 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639)).
Proof. exact (SYM (@lem3703566 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703568 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term559 B _42640 _42641 _42638 _42639) = (term613 B _42640 _42641 _42638 _42639).
Proof. exact (EQ_MP (@lem3703567 B _42640 _42641 _42638 _42639) (@lem0)). Qed.
Lemma lem3703569 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : term613 B _42640 _42641 _42638 _42639.
Proof. exact (EQ_MP (@lem3703568 B _42640 _42641 _42638 _42639) (@lem3702928 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703571 (b : Prop) (a : Prop) : (a \/ b) = (term569 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3703572 {B : Type'} (_42638 : B -> Prop) (_42639 : B -> Prop) (_42640 : B -> Prop) (_42641 : B -> Prop) : (term613 B _42640 _42641 _42638 _42639) = (term617 B _42638 _42639 _42640 _42641).
Proof. exact (@lem3703571 (term618 B _42640 _42641 _42638 _42639) (@SUBSET B _42640 _42641)). Qed.
Lemma lem3703574 (a : Prop) (b : Prop) : (term571 a b) = (term572 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3703575 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term619 B _42640 _42641 _42638 _42639) = (term620 B _42640 _42641 _42638 _42639).
Proof. exact (@lem3703574 (term609 B _42638 _42640) (term614 B _42641 _42638 _42639)). Qed.
Lemma lem3703577 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703578 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) : (term621 B _42638 _42640) = (_42638 = _42640).
Proof. exact (@lem3703577 (_42638 = _42640)). Qed.
Lemma lem3703579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3703580 {B : Type'} (_42638 : B -> Prop) (_42640 : B -> Prop) : (term622 B _42638 _42640) = (term623 B _42638 _42640).
Proof. exact (MK_COMB (@lem3703579) (@lem3703578 B _42638 _42640)). Qed.
Lemma lem3703582 (a : Prop) (b : Prop) : (term571 a b) = (term572 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3703583 {B : Type'} (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term624 B _42641 _42638 _42639) = (term625 B _42641 _42638 _42639).
Proof. exact (@lem3703582 (term609 B _42639 _42641) (term610 B _42638 _42639)). Qed.
Lemma lem3703585 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703586 {B : Type'} (_42639 : B -> Prop) (_42641 : B -> Prop) : (term621 B _42639 _42641) = (_42639 = _42641).
Proof. exact (@lem3703585 (_42639 = _42641)). Qed.
Lemma lem3703587 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3703588 {B : Type'} (_42639 : B -> Prop) (_42641 : B -> Prop) : (term622 B _42639 _42641) = (term623 B _42639 _42641).
Proof. exact (MK_COMB (@lem3703587) (@lem3703586 B _42639 _42641)). Qed.
Lemma lem3703590 (a : Prop) : (term575 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3703591 {B : Type'} (_42638 : B -> Prop) (_42639 : B -> Prop) : (term626 B _42638 _42639) = (@SUBSET B _42638 _42639).
Proof. exact (@lem3703590 (@SUBSET B _42638 _42639)). Qed.
Lemma lem3703592 {B : Type'} (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term625 B _42641 _42638 _42639) = (term627 B _42641 _42638 _42639).
Proof. exact (MK_COMB (@lem3703588 B _42639 _42641) (@lem3703591 B _42638 _42639)). Qed.
Lemma lem3703593 {B : Type'} (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term624 B _42641 _42638 _42639) = (term627 B _42641 _42638 _42639).
Proof. exact (TRANS (@lem3703583 B _42641 _42638 _42639) (@lem3703592 B _42641 _42638 _42639)). Qed.
Lemma lem3703594 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term620 B _42640 _42641 _42638 _42639) = (term628 B _42640 _42641 _42638 _42639).
Proof. exact (MK_COMB (@lem3703580 B _42638 _42640) (@lem3703593 B _42641 _42638 _42639)). Qed.
Lemma lem3703595 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term619 B _42640 _42641 _42638 _42639) = (term628 B _42640 _42641 _42638 _42639).
Proof. exact (TRANS (@lem3703575 B _42640 _42641 _42638 _42639) (@lem3703594 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703596 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3703597 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) (_42638 : B -> Prop) (_42639 : B -> Prop) : (term629 B _42640 _42641 _42638 _42639) = (term630 B _42640 _42641 _42638 _42639).
Proof. exact (MK_COMB (@lem3703596) (@lem3703595 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703598 {B : Type'} (_42640 : B -> Prop) (_42641 : B -> Prop) : (@SUBSET B _42640 _42641) = (@SUBSET B _42640 _42641).
Proof. exact (eq_refl (@SUBSET B _42640 _42641)). Qed.
Lemma lem3703599 {B : Type'} (_42638 : B -> Prop) (_42639 : B -> Prop) (_42640 : B -> Prop) (_42641 : B -> Prop) : (term617 B _42638 _42639 _42640 _42641) = (term631 B _42638 _42639 _42640 _42641).
Proof. exact (MK_COMB (@lem3703597 B _42640 _42641 _42638 _42639) (@lem3703598 B _42640 _42641)). Qed.
Lemma lem3703600 {B : Type'} (_42638 : B -> Prop) (_42639 : B -> Prop) (_42640 : B -> Prop) (_42641 : B -> Prop) : (term613 B _42640 _42641 _42638 _42639) = (term631 B _42638 _42639 _42640 _42641).
Proof. exact (TRANS (@lem3703572 B _42638 _42639 _42640 _42641) (@lem3703599 B _42638 _42639 _42640 _42641)). Qed.
Lemma lem3703602 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term632 A B s'' f s t.
Proof. exact (conj (@lem3703446 A B s'' s t f h2 h3) (@lem3703455 B t h1)). Qed.
Lemma lem3703603 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term633 A B s'' f s t.
Proof. exact (conj (@lem3703319 B t) (@lem3703602 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703605 {B : Type'} (_42638 : B -> Prop) (_42639 : B -> Prop) (_42640 : B -> Prop) (_42641 : B -> Prop) : term631 B _42638 _42639 _42640 _42641.
Proof. exact (EQ_MP (@lem3703600 B _42638 _42639 _42640 _42641) (@lem3703569 B _42640 _42641 _42638 _42639)). Qed.
Lemma lem3703606 {B : Type'} (_42638 : B -> Prop) (_42639 : B -> Prop) (_42640 : B -> Prop) (_42641 : B -> Prop) : term631 B _42638 _42639 _42640 _42641.
Proof. exact (@lem3703605 B _42638 _42639 _42640 _42641). Qed.
Lemma lem3703607 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term634 A B s'' f s t.
Proof. exact (@lem3703606 B t t t (term530 A B s'' f s t)). Qed.
Lemma lem3703610 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term635 A B s'' f s t.
Proof. exact (@lem3703607 A B s'' f s t (@lem3703603 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703611 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term636 A B s'' f s t.
Proof. exact (fun h0 : term637 A B s'' f s t => @lem3703610 A B s'' s t f h1 h2 h3). Qed.
Lemma lem3703613 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703614 {A B : Type'} (s'' : type525 A B) (f : A -> B) (s : A -> Prop) (t : B -> Prop) : (term636 A B s'' f s t) = (term635 A B s'' f s t).
Proof. exact (@lem3703613 (term635 A B s'' f s t)). Qed.
Lemma lem3703615 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term635 A B s'' f s t.
Proof. exact (EQ_MP (@lem3703614 A B s'' f s t) (@lem3703611 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703617 (a : Prop) (b : Prop) : (term638 a b) = (term639 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3703618 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term65 A B s t f _42612) = (term64 A B s t f _42612).
Proof. exact (@lem3703617 (@SUBSET A _42612 s) (term66 A B t f _42612)). Qed.
Lemma lem3703619 {A : Type'} (_42612 : A -> Prop) : (term67 A _42612) = (term67 A _42612).
Proof. exact (eq_refl (term67 A _42612)). Qed.
Lemma lem3703620 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term69 A B s t f _42612) = (term68 A B s t f _42612).
Proof. exact (MK_COMB (@lem3703619 A _42612) (@lem3703618 A B s t f _42612)). Qed.
Lemma lem3703622 (a : Prop) (b : Prop) : (term638 a b) = (term639 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3703623 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term68 A B s t f _42612) = (term70 A B s t f _42612).
Proof. exact (@lem3703622 (@FINITE A _42612) (term71 A B s t f _42612)). Qed.
Lemma lem3703624 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term69 A B s t f _42612) = (term70 A B s t f _42612).
Proof. exact (TRANS (@lem3703620 A B s t f _42612) (@lem3703623 A B s t f _42612)). Qed.
Lemma lem3703626 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3703627 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term70 A B s t f _42612) = (term640 A B s t f _42612).
Proof. exact (@lem3703626 (term54 A B s t f _42612)). Qed.
Lemma lem3703628 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (_42612 : A -> Prop) : (term69 A B s t f _42612) = (term640 A B s t f _42612).
Proof. exact (TRANS (@lem3703624 A B s t f _42612) (@lem3703627 A B s t f _42612)). Qed.
Lemma lem3703630 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term641 A B s'' f s t.
Proof. exact (conj (@lem3703310 A B s'' s t f h2 h3) (@lem3703615 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703631 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term642 A B s'' f s t.
Proof. exact (conj (@lem3703189 A B s'' s t f h2 h3) (@lem3703630 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703633 {A B : Type'} (_42612 : A -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term640 A B s t f _42612.
Proof. exact (EQ_MP (@lem3703628 A B s t f _42612) (@lem3702689 A B _42612 s t f h1)). Qed.
Lemma lem3703634 {A B : Type'} (_42612 : A -> Prop) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term640 A B s t f _42612.
Proof. exact (@lem3703633 A B _42612 s t f h1). Qed.
Lemma lem3703635 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term83 A B s t f) : term643 A B s'' f s t.
Proof. exact (@lem3703634 A B (s'' f s t) s t f h1). Qed.
Lemma lem3703638 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : False.
Proof. exact (@lem3703635 A B s'' s t f h3 (@lem3703631 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703639 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : term644.
Proof. exact (fun h0 : ~ False => @lem3703638 A B s'' s t f h1 h2 h3). Qed.
Lemma lem3703641 (p : Prop) : (term561 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3703642 : term644 = False.
Proof. exact (@lem3703641 False). Qed.
Lemma lem3703643 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : False.
Proof. exact (EQ_MP (@lem3703642) (@lem3703639 A B s'' s t f h1 h2 h3)). Qed.
Lemma lem3703644 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : (term11 B) = False.
Proof. exact (prop_ext (fun h4 : term11 B => @lem3703643 A B s'' s t f h1 h2 h3) (fun h4 : False => @lem3702207 B h1)). Qed.
Lemma lem3703645 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : False.
Proof. exact (EQ_MP (@lem3703644 A B s'' s t f h1 h2 h3) (@lem3702207 B h1)). Qed.
Lemma lem3703646 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : (term83 A B s t f) = False.
Proof. exact (prop_ext (fun h4 : term83 A B s t f => @lem3703645 A B s'' s t f h1 h2 h3) (fun h4 : False => @lem3702183 A B s t f h3)). Qed.
Lemma lem3703647 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : False.
Proof. exact (EQ_MP (@lem3703646 A B s'' s t f h1 h2 h3) (@lem3702183 A B s t f h3)). Qed.
Lemma lem3703648 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : (term516 A B s'') = False.
Proof. exact (prop_ext (fun h4 : term516 A B s'' => @lem3703647 A B s'' s t f h1 h2 h3) (fun h4 : False => @lem3701997 A B s'' h2)). Qed.
Lemma lem3703649 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : False.
Proof. exact (EQ_MP (@lem3703648 A B s'' s t f h1 h2 h3) (@lem3701997 A B s'' h2)). Qed.
Lemma lem3703650 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : (term11 B) = False.
Proof. exact (prop_ext (fun h4 : term11 B => @lem3703649 A B s'' s t f h1 h2 h3) (fun h4 : False => @lem3701727 B h1)). Qed.
Lemma lem3703651 {A B : Type'} (s'' : type525 A B) (s : A -> Prop) (t : B -> Prop) (f : A -> B) (h1 : term11 B) (h2 : term516 A B s'') (h3 : term83 A B s t f) : False.
Proof. exact (EQ_MP (@lem3703650 A B s'' s t f h1 h2 h3) (@lem3701727 B h1)). Qed.
Lemma lem3703652 {A B : Type'} (s : A -> Prop) (f : A -> B) (s'' : type525 A B) (h1 : term11 B) (h2 : term93 A B s f) (h3 : term516 A B s'') : False.
Proof. exact (ex_elim (@lem3701708 A B s f h2) (fun t : B -> Prop => fun h0 : term92 A B s f t => @lem3703651 A B s'' s t f h1 h3 h0)). Qed.
Lemma lem3703653 {A B : Type'} (f : A -> B) (s'' : type525 A B) (h1 : term11 B) (h2 : term100 A B f) (h3 : term516 A B s'') : False.
Proof. exact (ex_elim (@lem3701707 A B f h2) (fun s : A -> Prop => fun h0 : term99 A B f s => @lem3703652 A B s f s'' h1 h0 h3)). Qed.
Lemma lem3703654 {A B : Type'} (s'' : type525 A B) (h1 : term11 B) (h2 : term10 A B) (h3 : term516 A B s'') : False.
Proof. exact (ex_elim (@lem3699121 A B h2) (fun f : A -> B => fun h0 : term107 A B f => @lem3703653 A B f s'' h1 h0 h3)). Qed.
Lemma lem3703655 {A B : Type'} (s'' : type525 A B) (h1 : term13 A) (h2 : term11 B) (h3 : term10 A B) (h4 : term516 A B s'') : False.
Proof. exact (ex_elim (@lem3699973 A h1) (fun s''' : type483 A => fun h0 : term319 A s''' => @lem3703654 A B s'' h2 h3 h4)). Qed.
Lemma lem3703656 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term11 B) (h4 : term10 A B) : False.
Proof. exact (ex_elim (@lem3700825 A B h2) (fun s'' : type525 A B => fun h0 : term518 A B s'' => @lem3703655 A B s'' h1 h3 h4 h0)). Qed.
Lemma lem3703657 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term13 B) (h4 : term11 B) (h5 : term10 A B) : False.
Proof. exact (ex_elim (@lem3701677 B h3) (fun s' : type483 B => fun h0 : term319 B s' => @lem3703656 A B h1 h2 h4 h5)). Qed.
Lemma lem3703658 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term13 B) (h4 : term11 B) (h5 : term10 A B) : (term11 B) = False.
Proof. exact (prop_ext (fun h6 : term11 B => @lem3703657 A B h1 h2 h3 h4 h5) (fun h6 : False => @lem3701703 B h4)). Qed.
Lemma lem3703659 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term13 B) (h4 : term11 B) (h5 : term10 A B) : False.
Proof. exact (EQ_MP (@lem3703658 A B h1 h2 h3 h4 h5) (@lem3701703 B h4)). Qed.
Lemma lem3703660 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term13 B) (h4 : term10 A B) : term18 B.
Proof. exact (fun h0 : term11 B => @lem3703659 A B h1 h2 h3 h0 h4). Qed.
Lemma lem3703661 {B : Type'} : (term18 B) = (term19 B).
Proof. exact (@lem69 (term11 B)). Qed.
Lemma lem3703662 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term13 B) (h4 : term10 A B) : term19 B.
Proof. exact (EQ_MP (@lem3703661 B) (@lem3703660 A B h1 h2 h3 h4)). Qed.
Lemma lem3703663 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term13 B) (h4 : term10 A B) : term22 A B.
Proof. exact (fun h0 : term11 A => @lem3703662 A B h1 h2 h3 h4). Qed.
Lemma lem3703664 {A B : Type'} (h1 : term13 A) (h2 : term12 A B) (h3 : term10 A B) : term25 A B.
Proof. exact (fun h0 : term13 B => @lem3703663 A B h1 h2 h0 h3). Qed.
Lemma lem3703665 {A B : Type'} (h1 : term13 A) (h2 : term10 A B) : term28 A B.
Proof. exact (fun h0 : term12 A B => @lem3703664 A B h1 h0 h2). Qed.
Lemma lem3703666 {A B : Type'} (h1 : term10 A B) : term30 A B.
Proof. exact (fun h0 : term13 A => @lem3703665 A B h0 h1). Qed.
Lemma lem3703667 {A B : Type'} : term32 A B.
Proof. exact (fun h0 : term10 A B => @lem3703666 A B h0). Qed.
Lemma lem3703668 {A B : Type'} : term14 A B.
Proof. exact (EQ_MP (@lem3698943 A B) (@lem3703667 A B)). Qed.
Lemma lem3703670 {A B : Type'} : term14 A B.
Proof. exact (@lem3698421 A B (@lem3703668 A B)). Qed.
Lemma lem3703671 {A B : Type'} (h1 : term10 A B) : term29 A B.
Proof. exact (@lem3703670 A B (@lem3698394 A B h1)). Qed.
Lemma lem3703672 {A B : Type'} (h1 : term10 A B) : term27 A B.
Proof. exact (@lem3703671 A B h1 (@lem3698398 A)). Qed.
Lemma lem3703673 {A B : Type'} (h1 : term10 A B) : term24 A B.
Proof. exact (@lem3703672 A B h1 (@lem3698397 A B)). Qed.
Lemma lem3703674 {A B : Type'} (h1 : term10 A B) : term21 A B.
Proof. exact (@lem3703673 A B h1 (@lem3698402 B)). Qed.
Lemma lem3703675 {A B : Type'} (h1 : term10 A B) : term18 B.
Proof. exact (@lem3703674 A B h1 (@lem3698396 A)). Qed.
Lemma lem3703676 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (@lem3703675 A B h1 (@lem3698395 B)). Qed.
Lemma lem3703677 {A B : Type'} (h1 : term10 A B) : (term10 A B) = False.
Proof. exact (prop_ext (fun h2 : term10 A B => @lem3703676 A B h1) (fun h2 : False => @lem3698394 A B h1)). Qed.
Lemma lem3703678 {A B : Type'} (h1 : term10 A B) : False.
Proof. exact (EQ_MP (@lem3703677 A B h1) (@lem3698394 A B h1)). Qed.
Lemma lem3703679 {A B : Type'} : term9 A B.
Proof. exact (fun h0 : term10 A B => @lem3703678 A B h0). Qed.
Lemma lem3703680 {A B : Type'} : term8 A B.
Proof. exact (EQ_MP (@lem3698393 A B) (@lem3703679 A B)). Qed.
