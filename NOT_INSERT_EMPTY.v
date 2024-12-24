Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_INSERT_EMPTY_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm1857_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Lemma lem3278453 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3278454 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3278453 A s t). Qed.
Lemma lem3278455 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@EMPTY A)) = (term1 A x s).
Proof. exact (@lem3278454 A (@INSERT A x s) (@EMPTY A)). Qed.
Lemma lem3278464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3278465 {A : Type'} (x : A) (s : A -> Prop) : (term2 A x s) = (term3 A x s).
Proof. exact (MK_COMB (@lem3278464) (@lem3278455 A x s)). Qed.
Lemma lem3278466 {A : Type'} (x : A) : (term4 A x) = (term5 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3278465 A x s)). Qed.
Lemma lem3278467 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3278468 {A : Type'} (x : A) : (term6 A x) = (term7 A x).
Proof. exact (MK_COMB (@lem3278467 A) (@lem3278466 A x)). Qed.
Lemma lem3278473 {A : Type'} : (term8 A) = (term9 A).
Proof. exact (fun_ext (fun x : A => @lem3278468 A x)). Qed.
Lemma lem3278474 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278475 {A : Type'} : (term10 A) = (term11 A).
Proof. exact (MK_COMB (@lem3278474 A) (@lem3278473 A)). Qed.
Lemma lem3278480 {A : Type'} : (term11 A) = (term10 A).
Proof. exact (SYM (@lem3278475 A)). Qed.
Lemma lem3278496 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A x y s) = (term13 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3278497 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term12 A x y s) = (term13 A y x s).
Proof. exact (@lem3278496 A y x s). Qed.
Lemma lem3278498 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term12 A x' x s) = (term13 A x x' s).
Proof. exact (@lem3278497 A x x' s). Qed.
Lemma lem3278504 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3278505 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3278504 A P x). Qed.
Lemma lem3278506 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3278505 A s x'). Qed.
Lemma lem3278507 {A : Type'} (x' : A) (x : A) : (term14 A x' x) = (term14 A x' x).
Proof. exact (eq_refl (term14 A x' x)). Qed.
Lemma lem3278508 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term13 A x x' s) = (term15 A x s x').
Proof. exact (MK_COMB (@lem3278507 A x' x) (@lem3278506 A s x')). Qed.
Lemma lem3278511 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term12 A x' x s) = (term15 A x s x').
Proof. exact (TRANS (@lem3278498 A x x' s) (@lem3278508 A x s x')). Qed.
Lemma lem3278512 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3278513 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term16 A x' x s) = (term17 A x s x').
Proof. exact (MK_COMB (@lem3278512) (@lem3278511 A x s x')). Qed.
Lemma lem3278515 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem3278516 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3278515 A x). Qed.
Lemma lem3278517 {A : Type'} (x' : A) : (@IN A x' (@EMPTY A)) = False.
Proof. exact (@lem3278516 A x'). Qed.
Lemma lem3278518 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term12 A x' x s) = (@IN A x' (@EMPTY A))) = ((term15 A x s x') = False).
Proof. exact (MK_COMB (@lem3278513 A x s x') (@lem3278517 A x')). Qed.
Lemma lem3278520 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem3278521 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term15 A x s x') = False) = (term18 A x s x').
Proof. exact (@lem3278520 (term15 A x s x')). Qed.
Lemma lem3278526 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : ((term12 A x' x s) = (@IN A x' (@EMPTY A))) = (term18 A x s x').
Proof. exact (TRANS (@lem3278518 A x s x') (@lem3278521 A x s x')). Qed.
Lemma lem3278527 {A : Type'} (x : A) (s : A -> Prop) : (term19 A x s) = (term20 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3278526 A x s x')). Qed.
Lemma lem3278528 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278529 {A : Type'} (x : A) (s : A -> Prop) : (term1 A x s) = (term21 A x s).
Proof. exact (MK_COMB (@lem3278528 A) (@lem3278527 A x s)). Qed.
Lemma lem3278534 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3278535 {A : Type'} (x : A) (s : A -> Prop) : (term3 A x s) = (term22 A x s).
Proof. exact (MK_COMB (@lem3278534) (@lem3278529 A x s)). Qed.
Lemma lem3278536 {A : Type'} (x : A) : (term5 A x) = (term23 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3278535 A x s)). Qed.
Lemma lem3278537 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3278538 {A : Type'} (x : A) : (term7 A x) = (term24 A x).
Proof. exact (MK_COMB (@lem3278537 A) (@lem3278536 A x)). Qed.
Lemma lem3278543 {A : Type'} : (term9 A) = (term25 A).
Proof. exact (fun_ext (fun x : A => @lem3278538 A x)). Qed.
Lemma lem3278544 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278545 {A : Type'} : (term11 A) = (term26 A).
Proof. exact (MK_COMB (@lem3278544 A) (@lem3278543 A)). Qed.
Lemma lem3278550 {A : Type'} : (term26 A) = (term11 A).
Proof. exact (SYM (@lem3278545 A)). Qed.
Lemma lem3278552 (p : Prop) : p = (term27 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3278553 {A : Type'} : (term26 A) = (term28 A).
Proof. exact (@lem3278552 (term26 A)). Qed.
Lemma lem3278554 {A : Type'} : (term28 A) = (term26 A).
Proof. exact (SYM (@lem3278553 A)). Qed.
Lemma lem3278555 {A : Type'} (h1 : term29 A) : term29 A.
Proof. exact (h1). Qed.
Lemma lem3278558 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3278559 {A : Type'} : term30 A.
Proof. exact (fun h0 : term28 A => @lem3278558 A h0). Qed.
Lemma lem3278560 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3278561 {A : Type'} (h1 : term28 A) : term28 A.
Proof. exact (h1). Qed.
Lemma lem3278562 {A : Type'} (h1 : term28 A) (h2 : term30 A) : term28 A.
Proof. exact (@lem3278560 A h2 (@lem3278561 A h1)). Qed.
Lemma lem3278563 {A : Type'} (h1 : term28 A) : term31 A.
Proof. exact (fun h0 : term30 A => @lem3278562 A h1 h0). Qed.
Lemma lem3278564 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (h1). Qed.
Lemma lem3278565 {A : Type'} (h1 : term28 A) (h2 : term30 A) : term28 A.
Proof. exact (@lem3278563 A h1 (@lem3278564 A h2)). Qed.
Lemma lem3278566 {A : Type'} (h1 : term30 A) : term30 A.
Proof. exact (fun h0 : term28 A => @lem3278565 A h0 h1). Qed.
Lemma lem3278567 {A : Type'} : term32 A.
Proof. exact (fun h0 : term30 A => @lem3278566 A h0). Qed.
Lemma lem3278570 {A : Type'} : term30 A.
Proof. exact (@lem3278567 A (@lem3278559 A)). Qed.
Lemma lem3278571 {A : Type'} : term30 A.
Proof. exact (@lem3278570 A). Qed.
Lemma lem3278573 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3278574 {A : Type'} : (term28 A) = (term33 A).
Proof. exact (@lem3278573 (term29 A)). Qed.
Lemma lem3278576 (t : Prop) : (term34 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3278577 {A : Type'} : (term33 A) = (term26 A).
Proof. exact (@lem3278576 (term26 A)). Qed.
Lemma lem3278596 {A : Type'} : (term28 A) = (term26 A).
Proof. exact (TRANS (@lem3278574 A) (@lem3278577 A)). Qed.
Lemma lem3278603 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term18 A x s x') = (term18 A x s x').
Proof. exact (eq_refl (term18 A x s x')). Qed.
Lemma lem3278604 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term20 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3278603 A x s x')). Qed.
Lemma lem3278605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278606 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term21 A x s).
Proof. exact (MK_COMB (@lem3278605 A) (@lem3278604 A x s)). Qed.
Lemma lem3278607 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3278608 {A : Type'} (x : A) (s : A -> Prop) : (term22 A x s) = (term22 A x s).
Proof. exact (MK_COMB (@lem3278607) (@lem3278606 A x s)). Qed.
Lemma lem3278609 {A : Type'} (x : A) : (term23 A x) = (term23 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3278608 A x s)). Qed.
Lemma lem3278610 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3278611 {A : Type'} (x : A) : (term24 A x) = (term24 A x).
Proof. exact (MK_COMB (@lem3278610 A) (@lem3278609 A x)). Qed.
Lemma lem3278612 {A : Type'} : (term25 A) = (term25 A).
Proof. exact (fun_ext (fun x : A => @lem3278611 A x)). Qed.
Lemma lem3278613 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278614 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem3278613 A) (@lem3278612 A)). Qed.
Lemma lem3278637 {A : Type'} : (term28 A) = (term26 A).
Proof. exact (TRANS (@lem3278596 A) (@lem3278614 A)). Qed.
Lemma lem3278638 {A : Type'} : (term26 A) = (term28 A).
Proof. exact (SYM (@lem3278637 A)). Qed.
Lemma lem3278639 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term21 A x s.
Proof. exact (h1). Qed.
Lemma lem3278646 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term18 A x s x') = (term35 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3278647 {A : Type'} (x : A) (s : A -> Prop) : (term20 A x s) = (term36 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3278646 A x s x')). Qed.
Lemma lem3278648 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278649 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term37 A x s).
Proof. exact (MK_COMB (@lem3278648 A) (@lem3278647 A x s)). Qed.
Lemma lem3278651 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term38 A P Q) = (term39 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3278652 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term38 A P Q) = (term39 A P Q).
Proof. exact (@lem3278651 A P Q). Qed.
Lemma lem3278653 {A : Type'} (x : A) (s : A -> Prop) : (term40 A x s) = (term41 A x s).
Proof. exact (@lem3278652 A (term42 A x) (term43 A s)). Qed.
Lemma lem3278654 {A : Type'} (x' : A) (x : A) : (term44 A x x') = (term45 A x' x).
Proof. exact (eq_refl (term44 A x x')). Qed.
Lemma lem3278655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3278656 {A : Type'} (x' : A) (x : A) : (term46 A x x') = (term47 A x' x).
Proof. exact (MK_COMB (@lem3278655) (@lem3278654 A x' x)). Qed.
Lemma lem3278657 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term49 A s x').
Proof. exact (eq_refl (term48 A s x')). Qed.
Lemma lem3278658 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term50 A x s x') = (term35 A x s x').
Proof. exact (MK_COMB (@lem3278656 A x' x) (@lem3278657 A s x')). Qed.
Lemma lem3278659 {A : Type'} (x : A) (s : A -> Prop) : (term51 A x s) = (term36 A x s).
Proof. exact (fun_ext (fun x' : A => @lem3278658 A x s x')). Qed.
Lemma lem3278660 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278661 {A : Type'} (x : A) (s : A -> Prop) : (term40 A x s) = (term37 A x s).
Proof. exact (MK_COMB (@lem3278660 A) (@lem3278659 A x s)). Qed.
Lemma lem3278662 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3278663 {A : Type'} (x : A) (s : A -> Prop) : (term52 A x s) = (term53 A x s).
Proof. exact (MK_COMB (@lem3278662) (@lem3278661 A x s)). Qed.
Lemma lem3278664 {A : Type'} (x' : A) (x : A) : (term44 A x x') = (term45 A x' x).
Proof. exact (eq_refl (term44 A x x')). Qed.
Lemma lem3278665 {A : Type'} (x : A) : (term54 A x) = (term42 A x).
Proof. exact (fun_ext (fun x' : A => @lem3278664 A x' x)). Qed.
Lemma lem3278666 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278667 {A : Type'} (x : A) : (term55 A x) = (term56 A x).
Proof. exact (MK_COMB (@lem3278666 A) (@lem3278665 A x)). Qed.
Lemma lem3278668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3278669 {A : Type'} (x : A) : (term57 A x) = (term58 A x).
Proof. exact (MK_COMB (@lem3278668) (@lem3278667 A x)). Qed.
Lemma lem3278670 {A : Type'} (s : A -> Prop) (x' : A) : (term48 A s x') = (term49 A s x').
Proof. exact (eq_refl (term48 A s x')). Qed.
Lemma lem3278671 {A : Type'} (s : A -> Prop) : (term59 A s) = (term43 A s).
Proof. exact (fun_ext (fun x' : A => @lem3278670 A s x')). Qed.
Lemma lem3278672 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278673 {A : Type'} (s : A -> Prop) : (term60 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3278672 A) (@lem3278671 A s)). Qed.
Lemma lem3278674 {A : Type'} (x : A) (s : A -> Prop) : (term41 A x s) = (term62 A x s).
Proof. exact (MK_COMB (@lem3278669 A x) (@lem3278673 A s)). Qed.
Lemma lem3278675 {A : Type'} (x : A) (s : A -> Prop) : ((term40 A x s) = (term41 A x s)) = ((term37 A x s) = (term62 A x s)).
Proof. exact (MK_COMB (@lem3278663 A x s) (@lem3278674 A x s)). Qed.
Lemma lem3278686 {A : Type'} (x : A) (s : A -> Prop) : (term37 A x s) = (term62 A x s).
Proof. exact (EQ_MP (@lem3278675 A x s) (@lem3278653 A x s)). Qed.
Lemma lem3278687 {A : Type'} (x : A) (s : A -> Prop) : (term21 A x s) = (term62 A x s).
Proof. exact (TRANS (@lem3278649 A x s) (@lem3278686 A x s)). Qed.
Lemma lem3278688 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term62 A x s.
Proof. exact (EQ_MP (@lem3278687 A x s) (@lem3278639 A x s h1)). Qed.
Lemma lem3278693 {A : Type'} (s : A -> Prop) (x' : A) : (term49 A s x') = (term49 A s x').
Proof. exact (eq_refl (term49 A s x')). Qed.
Lemma lem3278694 {A : Type'} (s : A -> Prop) : (term43 A s) = (term43 A s).
Proof. exact (fun_ext (fun x' : A => @lem3278693 A s x')). Qed.
Lemma lem3278695 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278696 {A : Type'} (s : A -> Prop) : (term61 A s) = (term61 A s).
Proof. exact (MK_COMB (@lem3278695 A) (@lem3278694 A s)). Qed.
Lemma lem3278703 {A : Type'} (x' : A) (x : A) : (term45 A x' x) = (term45 A x' x).
Proof. exact (eq_refl (term45 A x' x)). Qed.
Lemma lem3278704 {A : Type'} (x : A) : (term42 A x) = (term42 A x).
Proof. exact (fun_ext (fun x' : A => @lem3278703 A x' x)). Qed.
Lemma lem3278705 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278706 {A : Type'} (x : A) : (term56 A x) = (term56 A x).
Proof. exact (MK_COMB (@lem3278705 A) (@lem3278704 A x)). Qed.
Lemma lem3278707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3278708 {A : Type'} (x : A) : (term58 A x) = (term58 A x).
Proof. exact (MK_COMB (@lem3278707) (@lem3278706 A x)). Qed.
Lemma lem3278709 {A : Type'} (x : A) (s : A -> Prop) : (term62 A x s) = (term62 A x s).
Proof. exact (MK_COMB (@lem3278708 A x) (@lem3278696 A s)). Qed.
Lemma lem3278710 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term62 A x s.
Proof. exact (EQ_MP (@lem3278709 A x s) (@lem3278688 A x s h1)). Qed.
Lemma lem3278712 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term56 A x.
Proof. exact (proj1 (@lem3278710 A x s h1)). Qed.
Lemma lem3278714 {A : Type'} (x' : A) (x : A) : (term45 A x' x) = (term45 A x' x).
Proof. exact (eq_refl (term45 A x' x)). Qed.
Lemma lem3278715 {A : Type'} (x : A) : (term42 A x) = (term42 A x).
Proof. exact (fun_ext (fun x' : A => @lem3278714 A x' x)). Qed.
Lemma lem3278716 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3278718 {A : Type'} (x : A) : (term56 A x) = (term56 A x).
Proof. exact (MK_COMB (@lem3278716 A) (@lem3278715 A x)). Qed.
Lemma lem3278719 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term56 A x.
Proof. exact (EQ_MP (@lem3278718 A x) (@lem3278712 A x s h1)). Qed.
Lemma lem3278727 {A : Type'} (_33578 : A) (x : A) (s : A -> Prop) (h1 : term21 A x s) : term44 A x _33578.
Proof. exact (@lem3278719 A x s h1 _33578). Qed.
Lemma lem3278728 {A : Type'} (_33578 : A) (x : A) : (term44 A x _33578) = (term45 A _33578 x).
Proof. exact (eq_refl (term44 A x _33578)). Qed.
Lemma lem3278734 {A : Type'} (_33578 : A) (x : A) (s : A -> Prop) (h1 : term21 A x s) : term45 A _33578 x.
Proof. exact (EQ_MP (@lem3278728 A _33578 x) (@lem3278727 A _33578 x s h1)). Qed.
Lemma lem3278752 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3278753 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3278752 A x). Qed.
Lemma lem3278754 {A : Type'} (x : A) : term63 A x.
Proof. exact (fun h0 : term64 A x => @lem3278753 A x). Qed.
Lemma lem3278756 (p : Prop) : (term65 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278757 {A : Type'} (x : A) : (term63 A x) = (x = x).
Proof. exact (@lem3278756 (x = x)). Qed.
Lemma lem3278758 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3278757 A x) (@lem3278754 A x)). Qed.
Lemma lem3278761 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278763 {A : Type'} (_33578 : A) (x : A) : (term45 A _33578 x) = (term66 A _33578 x).
Proof. exact (@lem3278761 (_33578 = x)). Qed.
Lemma lem3278766 {A : Type'} (_33578 : A) (x : A) (s : A -> Prop) (h1 : term21 A x s) : term66 A _33578 x.
Proof. exact (EQ_MP (@lem3278763 A _33578 x) (@lem3278734 A _33578 x s h1)). Qed.
Lemma lem3278767 {A : Type'} (_33578 : A) (x : A) (s : A -> Prop) (h1 : term21 A x s) : term66 A _33578 x.
Proof. exact (@lem3278766 A _33578 x s h1). Qed.
Lemma lem3278768 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term67 A x.
Proof. exact (@lem3278767 A x x s h1). Qed.
Lemma lem3278771 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : False.
Proof. exact (@lem3278768 A x s h1 (@lem3278758 A x)). Qed.
Lemma lem3278772 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : term68.
Proof. exact (fun h0 : ~ False => @lem3278771 A x s h1). Qed.
Lemma lem3278774 (p : Prop) : (term65 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278775 : term68 = False.
Proof. exact (@lem3278774 False). Qed.
Lemma lem3278776 {A : Type'} (x : A) (s : A -> Prop) (h1 : term21 A x s) : False.
Proof. exact (EQ_MP (@lem3278775) (@lem3278772 A x s h1)). Qed.
Lemma lem3278777 {A : Type'} (x : A) (s : A -> Prop) : term69 A x s.
Proof. exact (fun h0 : term21 A x s => @lem3278776 A x s h0). Qed.
Lemma lem3278778 {A : Type'} (x : A) (s : A -> Prop) : (term69 A x s) = (term22 A x s).
Proof. exact (@lem69 (term21 A x s)). Qed.
Lemma lem3278779 {A : Type'} (x : A) (s : A -> Prop) : term22 A x s.
Proof. exact (EQ_MP (@lem3278778 A x s) (@lem3278777 A x s)). Qed.
Lemma lem3278784 {A : Type'} (x : A) : term24 A x.
Proof. exact (fun s : A -> Prop => @lem3278779 A x s). Qed.
Lemma lem3278789 {A : Type'} : term26 A.
Proof. exact (fun x : A => @lem3278784 A x). Qed.
Lemma lem3278790 {A : Type'} : term28 A.
Proof. exact (EQ_MP (@lem3278638 A) (@lem3278789 A)). Qed.
Lemma lem3278792 {A : Type'} : term28 A.
Proof. exact (@lem3278571 A (@lem3278790 A)). Qed.
Lemma lem3278793 {A : Type'} (h1 : term29 A) : False.
Proof. exact (@lem3278792 A (@lem3278555 A h1)). Qed.
Lemma lem3278794 {A : Type'} (h1 : term29 A) : (term29 A) = False.
Proof. exact (prop_ext (fun h2 : term29 A => @lem3278793 A h1) (fun h2 : False => @lem3278555 A h1)). Qed.
Lemma lem3278795 {A : Type'} (h1 : term29 A) : False.
Proof. exact (EQ_MP (@lem3278794 A h1) (@lem3278555 A h1)). Qed.
Lemma lem3278796 {A : Type'} : term28 A.
Proof. exact (fun h0 : term29 A => @lem3278795 A h0). Qed.
Lemma lem3278797 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem3278554 A) (@lem3278796 A)). Qed.
Lemma lem3278798 {A : Type'} : term11 A.
Proof. exact (EQ_MP (@lem3278550 A) (@lem3278797 A)). Qed.
Lemma lem3278799 {A : Type'} : term10 A.
Proof. exact (EQ_MP (@lem3278480 A) (@lem3278798 A)). Qed.
