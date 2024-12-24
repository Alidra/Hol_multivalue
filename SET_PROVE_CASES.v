Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_PROVE_CASES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import SET_CASES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
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
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem3449347 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3449348 {A : Type'} : (term1 A) = (term2 A).
Proof. exact (@lem3449347 (term1 A)). Qed.
Lemma lem3449349 {A : Type'} : (term2 A) = (term1 A).
Proof. exact (SYM (@lem3449348 A)). Qed.
Lemma lem3449350 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3449351 {A : Type'} : term4 A.
Proof. exact (@lem3275014 A). Qed.
Lemma lem3449356 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem3449357 {A : Type'} : term6 A.
Proof. exact (fun h0 : term5 A => @lem3449356 A h0). Qed.
Lemma lem3449358 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem3449359 {A : Type'} (h1 : term5 A) : term5 A.
Proof. exact (h1). Qed.
Lemma lem3449360 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem3449358 A h2 (@lem3449359 A h1)). Qed.
Lemma lem3449361 {A : Type'} (h1 : term5 A) : term7 A.
Proof. exact (fun h0 : term6 A => @lem3449360 A h1 h0). Qed.
Lemma lem3449362 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (h1). Qed.
Lemma lem3449363 {A : Type'} (h1 : term5 A) (h2 : term6 A) : term5 A.
Proof. exact (@lem3449361 A h1 (@lem3449362 A h2)). Qed.
Lemma lem3449364 {A : Type'} (h1 : term6 A) : term6 A.
Proof. exact (fun h0 : term5 A => @lem3449363 A h0 h1). Qed.
Lemma lem3449365 {A : Type'} : term8 A.
Proof. exact (fun h0 : term6 A => @lem3449364 A h0). Qed.
Lemma lem3449368 {A : Type'} : term6 A.
Proof. exact (@lem3449365 A (@lem3449357 A)). Qed.
Lemma lem3449369 {A : Type'} : term6 A.
Proof. exact (@lem3449368 A). Qed.
Lemma lem3449395 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3449396 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem3449395 (term4 A)). Qed.
Lemma lem3449501 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (eq_refl (term11 A)). Qed.
Lemma lem3449508 {A : Type'} : (term5 A) = (term12 A).
Proof. exact (MK_COMB (@lem3449501 A) (@lem3449396 A)). Qed.
Lemma lem3449515 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s x t) = (term13 A s x t).
Proof. exact (eq_refl (term13 A s x t)). Qed.
Lemma lem3449516 {A : Type'} (s : A -> Prop) (x : A) : (term14 A s x) = (term14 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3449515 A s x t)). Qed.
Lemma lem3449517 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449518 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = (term15 A s x).
Proof. exact (MK_COMB (@lem3449517 A) (@lem3449516 A s x)). Qed.
Lemma lem3449519 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3449518 A s x)). Qed.
Lemma lem3449520 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3449521 {A : Type'} (s : A -> Prop) : (term17 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3449520 A) (@lem3449519 A s)). Qed.
Lemma lem3449524 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3449525 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3449524 A s) (@lem3449521 A s)). Qed.
Lemma lem3449526 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449525 A s)). Qed.
Lemma lem3449527 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449528 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem3449527 A) (@lem3449526 A)). Qed.
Lemma lem3449529 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3449530 {A : Type'} : (term10 A) = (term10 A).
Proof. exact (MK_COMB (@lem3449529) (@lem3449528 A)). Qed.
Lemma lem3449531 {A : Type'} (P : type686 A) (s : A -> Prop) : (P s) = (P s).
Proof. exact (eq_refl (P s)). Qed.
Lemma lem3449532 {A : Type'} (P : type686 A) : (term21 A P) = (term21 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449531 A P s)). Qed.
Lemma lem3449533 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449534 {A : Type'} (P : type686 A) : (term22 A P) = (term22 A P).
Proof. exact (MK_COMB (@lem3449533 A) (@lem3449532 A P)). Qed.
Lemma lem3449541 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term23 A P a s) = (term23 A P a s).
Proof. exact (eq_refl (term23 A P a s)). Qed.
Lemma lem3449542 {A : Type'} (P : type686 A) (a : A) : (term24 A P a) = (term24 A P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449541 A P a s)). Qed.
Lemma lem3449543 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449544 {A : Type'} (P : type686 A) (a : A) : (term25 A P a) = (term25 A P a).
Proof. exact (MK_COMB (@lem3449543 A) (@lem3449542 A P a)). Qed.
Lemma lem3449545 {A : Type'} (P : type686 A) : (term26 A P) = (term26 A P).
Proof. exact (fun_ext (fun a : A => @lem3449544 A P a)). Qed.
Lemma lem3449546 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3449547 {A : Type'} (P : type686 A) : (term27 A P) = (term27 A P).
Proof. exact (MK_COMB (@lem3449546 A) (@lem3449545 A P)). Qed.
Lemma lem3449550 {A : Type'} (P : type686 A) : (term28 A P) = (term28 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem3449551 {A : Type'} (P : type686 A) : (term29 A P) = (term29 A P).
Proof. exact (MK_COMB (@lem3449550 A P) (@lem3449547 A P)). Qed.
Lemma lem3449552 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3449553 {A : Type'} (P : type686 A) : (term30 A P) = (term30 A P).
Proof. exact (MK_COMB (@lem3449552) (@lem3449551 A P)). Qed.
Lemma lem3449554 {A : Type'} (P : type686 A) : (term31 A P) = (term31 A P).
Proof. exact (MK_COMB (@lem3449553 A P) (@lem3449534 A P)). Qed.
Lemma lem3449555 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3449554 A P)). Qed.
Lemma lem3449556 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem3449557 {A : Type'} : (term1 A) = (term1 A).
Proof. exact (MK_COMB (@lem3449556 A) (@lem3449555 A)). Qed.
Lemma lem3449558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3449559 {A : Type'} : (term3 A) = (term3 A).
Proof. exact (MK_COMB (@lem3449558) (@lem3449557 A)). Qed.
Lemma lem3449560 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3449561 {A : Type'} : (term11 A) = (term11 A).
Proof. exact (MK_COMB (@lem3449560) (@lem3449559 A)). Qed.
Lemma lem3449562 {A : Type'} : (term12 A) = (term12 A).
Proof. exact (MK_COMB (@lem3449561 A) (@lem3449530 A)). Qed.
Lemma lem3449619 {A : Type'} : (term5 A) = (term12 A).
Proof. exact (TRANS (@lem3449508 A) (@lem3449562 A)). Qed.
Lemma lem3449620 {A : Type'} : (term12 A) = (term5 A).
Proof. exact (SYM (@lem3449619 A)). Qed.
Lemma lem3449621 {A : Type'} (h1 : term3 A) : term3 A.
Proof. exact (h1). Qed.
Lemma lem3449622 {A : Type'} (h1 : term4 A) : term4 A.
Proof. exact (h1). Qed.
Lemma lem3449626 {A : Type'} (a : A) (s : A -> Prop) : (term33 A a s) = (@IN A a s).
Proof. exact (@lem16933 (@IN A a s)). Qed.
Lemma lem3449627 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term34 A P a s) = (term34 A P a s).
Proof. exact (eq_refl (term34 A P a s)). Qed.
Lemma lem3449628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3449629 {A : Type'} (a : A) (s : A -> Prop) : (term35 A a s) = (term36 A a s).
Proof. exact (MK_COMB (@lem3449628) (@lem3449626 A a s)). Qed.
Lemma lem3449630 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term37 A P a s) = (term38 A P a s).
Proof. exact (MK_COMB (@lem3449629 A a s) (@lem3449627 A P a s)). Qed.
Lemma lem3449631 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term23 A P a s) = (term37 A P a s).
Proof. exact (@lem17265 (term39 A a s) (term34 A P a s)). Qed.
Lemma lem3449632 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term23 A P a s) = (term38 A P a s).
Proof. exact (TRANS (@lem3449631 A P a s) (@lem3449630 A P a s)). Qed.
Lemma lem3449633 {A : Type'} (P : type686 A) (a : A) : (term24 A P a) = (term40 A P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449632 A P a s)). Qed.
Lemma lem3449634 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449635 {A : Type'} (P : type686 A) (a : A) : (term25 A P a) = (term41 A P a).
Proof. exact (MK_COMB (@lem3449634 A) (@lem3449633 A P a)). Qed.
Lemma lem3449636 {A : Type'} (P : type686 A) : (term26 A P) = (term42 A P).
Proof. exact (fun_ext (fun a : A => @lem3449635 A P a)). Qed.
Lemma lem3449637 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3449638 {A : Type'} (P : type686 A) : (term27 A P) = (term43 A P).
Proof. exact (MK_COMB (@lem3449637 A) (@lem3449636 A P)). Qed.
Lemma lem3449640 {A : Type'} (P : type686 A) : (term28 A P) = (term28 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem3449641 {A : Type'} (P : type686 A) : (term29 A P) = (term44 A P).
Proof. exact (MK_COMB (@lem3449640 A P) (@lem3449638 A P)). Qed.
Lemma lem3449643 {A : Type'} (P : type686 A) : (term45 A P) = (term46 A P).
Proof. exact (@lem18392 (A -> Prop) P). Qed.
Lemma lem3449644 {A : Type'} (P : type686 A) : (term47 A P) = (term48 A P).
Proof. exact (@lem3449643 A (term21 A P)). Qed.
Lemma lem3449645 {A : Type'} (P : type686 A) (s : A -> Prop) : (term49 A P s) = (P s).
Proof. exact (eq_refl (term49 A P s)). Qed.
Lemma lem3449646 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3449648 {A : Type'} (P : type686 A) (s : A -> Prop) : (term50 A P s) = (term51 A P s).
Proof. exact (MK_COMB (@lem3449646) (@lem3449645 A P s)). Qed.
Lemma lem3449649 {A : Type'} (P : type686 A) : (term52 A P) = (term53 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449648 A P s)). Qed.
Lemma lem3449650 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449651 {A : Type'} (P : type686 A) : (term48 A P) = (term46 A P).
Proof. exact (MK_COMB (@lem3449650 A) (@lem3449649 A P)). Qed.
Lemma lem3449652 {A : Type'} (P : type686 A) : (term47 A P) = (term46 A P).
Proof. exact (TRANS (@lem3449644 A P) (@lem3449651 A P)). Qed.
Lemma lem3449653 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3449654 {A : Type'} (P : type686 A) : (term54 A P) = (term55 A P).
Proof. exact (MK_COMB (@lem3449653) (@lem3449641 A P)). Qed.
Lemma lem3449655 {A : Type'} (P : type686 A) : (term56 A P) = (term57 A P).
Proof. exact (MK_COMB (@lem3449654 A P) (@lem3449652 A P)). Qed.
Lemma lem3449656 {A : Type'} (P : type686 A) : (term58 A P) = (term56 A P).
Proof. exact (@lem17362 (term29 A P) (term22 A P)). Qed.
Lemma lem3449657 {A : Type'} (P : type686 A) : (term58 A P) = (term57 A P).
Proof. exact (TRANS (@lem3449656 A P) (@lem3449655 A P)). Qed.
Lemma lem3449658 {A : Type'} (P : type180 A) : (term59 A P) = (term60 A P).
Proof. exact (@lem18392 (type686 A) P). Qed.
Lemma lem3449659 {A : Type'} : (term3 A) = (term61 A).
Proof. exact (@lem3449658 A (term32 A)). Qed.
Lemma lem3449660 {A : Type'} (P : type686 A) : (term62 A P) = (term31 A P).
Proof. exact (eq_refl (term62 A P)). Qed.
Lemma lem3449661 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3449662 {A : Type'} (P : type686 A) : (term63 A P) = (term58 A P).
Proof. exact (MK_COMB (@lem3449661) (@lem3449660 A P)). Qed.
Lemma lem3449663 {A : Type'} (P : type686 A) : (term63 A P) = (term57 A P).
Proof. exact (TRANS (@lem3449662 A P) (@lem3449657 A P)). Qed.
Lemma lem3449664 {A : Type'} : (term64 A) = (term65 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3449663 A P)). Qed.
Lemma lem3449665 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem3449666 {A : Type'} : (term61 A) = (term66 A).
Proof. exact (MK_COMB (@lem3449665 A) (@lem3449664 A)). Qed.
Lemma lem3449667 {A : Type'} : (term3 A) = (term66 A).
Proof. exact (TRANS (@lem3449659 A) (@lem3449666 A)). Qed.
Lemma lem3449774 {A : Type'} (P : Prop) (Q : A -> Prop) : (term67 A P Q) = (term68 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3449775 {A : Type'} (P : Prop) (Q : type686 A) : (term69 A P Q) = (term70 A P Q).
Proof. exact (@lem3449774 (A -> Prop) P Q). Qed.
Lemma lem3449776 {A : Type'} (P : type686 A) : (term71 A P) = (term72 A P).
Proof. exact (@lem3449775 A (term44 A P) (term53 A P)). Qed.
Lemma lem3449777 {A : Type'} (P : type686 A) (s : A -> Prop) : (term73 A P s) = (term51 A P s).
Proof. exact (eq_refl (term73 A P s)). Qed.
Lemma lem3449778 {A : Type'} (P : type686 A) : (term74 A P) = (term53 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449777 A P s)). Qed.
Lemma lem3449779 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449780 {A : Type'} (P : type686 A) : (term75 A P) = (term46 A P).
Proof. exact (MK_COMB (@lem3449779 A) (@lem3449778 A P)). Qed.
Lemma lem3449781 {A : Type'} (P : type686 A) : (term55 A P) = (term55 A P).
Proof. exact (eq_refl (term55 A P)). Qed.
Lemma lem3449782 {A : Type'} (P : type686 A) : (term71 A P) = (term57 A P).
Proof. exact (MK_COMB (@lem3449781 A P) (@lem3449780 A P)). Qed.
Lemma lem3449783 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3449784 {A : Type'} (P : type686 A) : (term76 A P) = (term77 A P).
Proof. exact (MK_COMB (@lem3449783) (@lem3449782 A P)). Qed.
Lemma lem3449785 {A : Type'} (P : type686 A) (s : A -> Prop) : (term73 A P s) = (term51 A P s).
Proof. exact (eq_refl (term73 A P s)). Qed.
Lemma lem3449786 {A : Type'} (P : type686 A) : (term55 A P) = (term55 A P).
Proof. exact (eq_refl (term55 A P)). Qed.
Lemma lem3449787 {A : Type'} (P : type686 A) (s : A -> Prop) : (term78 A P s) = (term79 A P s).
Proof. exact (MK_COMB (@lem3449786 A P) (@lem3449785 A P s)). Qed.
Lemma lem3449788 {A : Type'} (P : type686 A) : (term80 A P) = (term81 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449787 A P s)). Qed.
Lemma lem3449789 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449790 {A : Type'} (P : type686 A) : (term72 A P) = (term82 A P).
Proof. exact (MK_COMB (@lem3449789 A) (@lem3449788 A P)). Qed.
Lemma lem3449791 {A : Type'} (P : type686 A) : ((term71 A P) = (term72 A P)) = ((term57 A P) = (term82 A P)).
Proof. exact (MK_COMB (@lem3449784 A P) (@lem3449790 A P)). Qed.
Lemma lem3449792 {A : Type'} (P : type686 A) : (term57 A P) = (term82 A P).
Proof. exact (EQ_MP (@lem3449791 A P) (@lem3449776 A P)). Qed.
Lemma lem3449793 {A : Type'} : (term65 A) = (term83 A).
Proof. exact (fun_ext (fun P : type686 A => @lem3449792 A P)). Qed.
Lemma lem3449794 {A : Type'} : (@ex ((A -> Prop) -> Prop)) = (@ex ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> Prop))). Qed.
Lemma lem3449796 {A : Type'} : (term66 A) = (term84 A).
Proof. exact (MK_COMB (@lem3449794 A) (@lem3449793 A)). Qed.
Lemma lem3449797 {A : Type'} : (term3 A) = (term84 A).
Proof. exact (TRANS (@lem3449667 A) (@lem3449796 A)). Qed.
Lemma lem3449798 {A : Type'} (h1 : term3 A) : term84 A.
Proof. exact (EQ_MP (@lem3449797 A) (@lem3449621 A h1)). Qed.
Lemma lem3449804 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term13 A s x t) = (term13 A s x t).
Proof. exact (eq_refl (term13 A s x t)). Qed.
Lemma lem3449805 {A : Type'} (s : A -> Prop) (x : A) : (term14 A s x) = (term14 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3449804 A s x t)). Qed.
Lemma lem3449806 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449807 {A : Type'} (s : A -> Prop) (x : A) : (term15 A s x) = (term15 A s x).
Proof. exact (MK_COMB (@lem3449806 A) (@lem3449805 A s x)). Qed.
Lemma lem3449808 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3449807 A s x)). Qed.
Lemma lem3449809 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3449810 {A : Type'} (s : A -> Prop) : (term17 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3449809 A) (@lem3449808 A s)). Qed.
Lemma lem3449812 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3449813 {A : Type'} (s : A -> Prop) : (term19 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3449812 A s) (@lem3449810 A s)). Qed.
Lemma lem3449814 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449813 A s)). Qed.
Lemma lem3449815 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449816 {A : Type'} : (term4 A) = (term4 A).
Proof. exact (MK_COMB (@lem3449815 A) (@lem3449814 A)). Qed.
Lemma lem3449919 {A : Type'} (P : Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3449920 {A : Type'} (P : Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (@lem3449919 A P Q). Qed.
Lemma lem3449921 {A : Type'} (s : A -> Prop) : (term87 A s) = (term88 A s).
Proof. exact (@lem3449920 A (s = (@EMPTY A)) (term16 A s)). Qed.
Lemma lem3449922 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term15 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3449923 {A : Type'} (s : A -> Prop) : (term90 A s) = (term16 A s).
Proof. exact (fun_ext (fun x : A => @lem3449922 A s x)). Qed.
Lemma lem3449924 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3449925 {A : Type'} (s : A -> Prop) : (term91 A s) = (term17 A s).
Proof. exact (MK_COMB (@lem3449924 A) (@lem3449923 A s)). Qed.
Lemma lem3449926 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3449927 {A : Type'} (s : A -> Prop) : (term87 A s) = (term19 A s).
Proof. exact (MK_COMB (@lem3449926 A s) (@lem3449925 A s)). Qed.
Lemma lem3449928 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3449929 {A : Type'} (s : A -> Prop) : (term92 A s) = (term93 A s).
Proof. exact (MK_COMB (@lem3449928) (@lem3449927 A s)). Qed.
Lemma lem3449930 {A : Type'} (s : A -> Prop) (x : A) : (term89 A s x) = (term15 A s x).
Proof. exact (eq_refl (term89 A s x)). Qed.
Lemma lem3449931 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3449932 {A : Type'} (s : A -> Prop) (x : A) : (term94 A s x) = (term95 A s x).
Proof. exact (MK_COMB (@lem3449931 A s) (@lem3449930 A s x)). Qed.
Lemma lem3449933 {A : Type'} (s : A -> Prop) : (term96 A s) = (term97 A s).
Proof. exact (fun_ext (fun x : A => @lem3449932 A s x)). Qed.
Lemma lem3449934 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3449935 {A : Type'} (s : A -> Prop) : (term88 A s) = (term98 A s).
Proof. exact (MK_COMB (@lem3449934 A) (@lem3449933 A s)). Qed.
Lemma lem3449936 {A : Type'} (s : A -> Prop) : ((term87 A s) = (term88 A s)) = ((term19 A s) = (term98 A s)).
Proof. exact (MK_COMB (@lem3449929 A s) (@lem3449935 A s)). Qed.
Lemma lem3449937 {A : Type'} (s : A -> Prop) : (term19 A s) = (term98 A s).
Proof. exact (EQ_MP (@lem3449936 A s) (@lem3449921 A s)). Qed.
Lemma lem3449939 {A : Type'} (P : Prop) (Q : A -> Prop) : (term85 A P Q) = (term86 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3449940 {A : Type'} (P : Prop) (Q : type686 A) : (term99 A P Q) = (term100 A P Q).
Proof. exact (@lem3449939 (A -> Prop) P Q). Qed.
Lemma lem3449941 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term102 A s x).
Proof. exact (@lem3449940 A (s = (@EMPTY A)) (term14 A s x)). Qed.
Lemma lem3449942 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term103 A s x t) = (term13 A s x t).
Proof. exact (eq_refl (term103 A s x t)). Qed.
Lemma lem3449943 {A : Type'} (s : A -> Prop) (x : A) : (term104 A s x) = (term14 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3449942 A s x t)). Qed.
Lemma lem3449944 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449945 {A : Type'} (s : A -> Prop) (x : A) : (term105 A s x) = (term15 A s x).
Proof. exact (MK_COMB (@lem3449944 A) (@lem3449943 A s x)). Qed.
Lemma lem3449946 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3449947 {A : Type'} (s : A -> Prop) (x : A) : (term101 A s x) = (term95 A s x).
Proof. exact (MK_COMB (@lem3449946 A s) (@lem3449945 A s x)). Qed.
Lemma lem3449948 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3449949 {A : Type'} (s : A -> Prop) (x : A) : (term106 A s x) = (term107 A s x).
Proof. exact (MK_COMB (@lem3449948) (@lem3449947 A s x)). Qed.
Lemma lem3449950 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term103 A s x t) = (term13 A s x t).
Proof. exact (eq_refl (term103 A s x t)). Qed.
Lemma lem3449951 {A : Type'} (s : A -> Prop) : (term18 A s) = (term18 A s).
Proof. exact (eq_refl (term18 A s)). Qed.
Lemma lem3449952 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term108 A s x t) = (term109 A s x t).
Proof. exact (MK_COMB (@lem3449951 A s) (@lem3449950 A s x t)). Qed.
Lemma lem3449953 {A : Type'} (s : A -> Prop) (x : A) : (term110 A s x) = (term111 A s x).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3449952 A s x t)). Qed.
Lemma lem3449954 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3449955 {A : Type'} (s : A -> Prop) (x : A) : (term102 A s x) = (term112 A s x).
Proof. exact (MK_COMB (@lem3449954 A) (@lem3449953 A s x)). Qed.
Lemma lem3449956 {A : Type'} (s : A -> Prop) (x : A) : ((term101 A s x) = (term102 A s x)) = ((term95 A s x) = (term112 A s x)).
Proof. exact (MK_COMB (@lem3449949 A s x) (@lem3449955 A s x)). Qed.
Lemma lem3449957 {A : Type'} (s : A -> Prop) (x : A) : (term95 A s x) = (term112 A s x).
Proof. exact (EQ_MP (@lem3449956 A s x) (@lem3449941 A s x)). Qed.
Lemma lem3449958 {A : Type'} (s : A -> Prop) : (term97 A s) = (term113 A s).
Proof. exact (fun_ext (fun x : A => @lem3449957 A s x)). Qed.
Lemma lem3449959 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3449960 {A : Type'} (s : A -> Prop) : (term98 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem3449959 A) (@lem3449958 A s)). Qed.
Lemma lem3449961 {A : Type'} (s : A -> Prop) : (term19 A s) = (term114 A s).
Proof. exact (TRANS (@lem3449937 A s) (@lem3449960 A s)). Qed.
Lemma lem3449962 {A : Type'} : (term20 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449961 A s)). Qed.
Lemma lem3449963 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449964 {A : Type'} : (term4 A) = (term116 A).
Proof. exact (MK_COMB (@lem3449963 A) (@lem3449962 A)). Qed.
Lemma lem3449966 {A B : Type'} (P : type1413 A B) : (term117 A B P) = (term118 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3449967 {A : Type'} (P : type672 A) : (term119 A P) = (term120 A P).
Proof. exact (@lem3449966 (A -> Prop) A P). Qed.
Lemma lem3449968 {A : Type'} : (term121 A) = (term122 A).
Proof. exact (@lem3449967 A (term123 A)). Qed.
Lemma lem3449969 {A : Type'} (s : A -> Prop) : (term124 A s) = (term113 A s).
Proof. exact (eq_refl (term124 A s)). Qed.
Lemma lem3449970 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3449971 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term126 A s x).
Proof. exact (MK_COMB (@lem3449969 A s) (@lem3449970 A x)). Qed.
Lemma lem3449972 {A : Type'} (s : A -> Prop) (x : A) : (term126 A s x) = (term112 A s x).
Proof. exact (eq_refl (term126 A s x)). Qed.
Lemma lem3449973 {A : Type'} (s : A -> Prop) (x : A) : (term125 A s x) = (term112 A s x).
Proof. exact (TRANS (@lem3449971 A s x) (@lem3449972 A s x)). Qed.
Lemma lem3449974 {A : Type'} (s : A -> Prop) : (term127 A s) = (term113 A s).
Proof. exact (fun_ext (fun x : A => @lem3449973 A s x)). Qed.
Lemma lem3449975 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3449976 {A : Type'} (s : A -> Prop) : (term128 A s) = (term114 A s).
Proof. exact (MK_COMB (@lem3449975 A) (@lem3449974 A s)). Qed.
Lemma lem3449977 {A : Type'} : (term129 A) = (term115 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449976 A s)). Qed.
Lemma lem3449978 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449979 {A : Type'} : (term121 A) = (term116 A).
Proof. exact (MK_COMB (@lem3449978 A) (@lem3449977 A)). Qed.
Lemma lem3449980 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3449981 {A : Type'} : (term130 A) = (term131 A).
Proof. exact (MK_COMB (@lem3449980) (@lem3449979 A)). Qed.
Lemma lem3449982 {A : Type'} (s : A -> Prop) : (term124 A s) = (term113 A s).
Proof. exact (eq_refl (term124 A s)). Qed.
Lemma lem3449983 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3449984 {A : Type'} (x : type684 A) (s : A -> Prop) : (term132 A x s) = (term133 A x s).
Proof. exact (MK_COMB (@lem3449982 A s) (@lem3449983 A x s)). Qed.
Lemma lem3449985 {A : Type'} (x : type684 A) (s : A -> Prop) : (term133 A x s) = (term134 A x s).
Proof. exact (eq_refl (term133 A x s)). Qed.
Lemma lem3449986 {A : Type'} (x : type684 A) (s : A -> Prop) : (term132 A x s) = (term134 A x s).
Proof. exact (TRANS (@lem3449984 A x s) (@lem3449985 A x s)). Qed.
Lemma lem3449987 {A : Type'} (x : type684 A) : (term135 A x) = (term136 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3449986 A x s)). Qed.
Lemma lem3449988 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3449989 {A : Type'} (x : type684 A) : (term137 A x) = (term138 A x).
Proof. exact (MK_COMB (@lem3449988 A) (@lem3449987 A x)). Qed.
Lemma lem3449990 {A : Type'} : (term139 A) = (term140 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3449989 A x)). Qed.
Lemma lem3449991 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3449992 {A : Type'} : (term122 A) = (term141 A).
Proof. exact (MK_COMB (@lem3449991 A) (@lem3449990 A)). Qed.
Lemma lem3449993 {A : Type'} : ((term121 A) = (term122 A)) = ((term116 A) = (term141 A)).
Proof. exact (MK_COMB (@lem3449981 A) (@lem3449992 A)). Qed.
Lemma lem3449994 {A : Type'} : (term116 A) = (term141 A).
Proof. exact (EQ_MP (@lem3449993 A) (@lem3449968 A)). Qed.
Lemma lem3449996 {A B : Type'} (P : type1413 A B) : (term117 A B P) = (term118 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3449997 {A : Type'} (P : type639 A) : (term142 A P) = (term143 A P).
Proof. exact (@lem3449996 (A -> Prop) (A -> Prop) P). Qed.
Lemma lem3449998 {A : Type'} (x : type684 A) : (term144 A x) = (term145 A x).
Proof. exact (@lem3449997 A (term146 A x)). Qed.
Lemma lem3449999 {A : Type'} (x : type684 A) (s : A -> Prop) : (term147 A x s) = (term148 A x s).
Proof. exact (eq_refl (term147 A x s)). Qed.
Lemma lem3450000 {A : Type'} (t : A -> Prop) : t = t.
Proof. exact (eq_refl t). Qed.
Lemma lem3450001 {A : Type'} (x : type684 A) (s : A -> Prop) (t : A -> Prop) : (term149 A x s t) = (term150 A x s t).
Proof. exact (MK_COMB (@lem3449999 A x s) (@lem3450000 A t)). Qed.
Lemma lem3450002 {A : Type'} (x : type684 A) (s : A -> Prop) (t : A -> Prop) : (term150 A x s t) = (term151 A x s t).
Proof. exact (eq_refl (term150 A x s t)). Qed.
Lemma lem3450003 {A : Type'} (x : type684 A) (s : A -> Prop) (t : A -> Prop) : (term149 A x s t) = (term151 A x s t).
Proof. exact (TRANS (@lem3450001 A x s t) (@lem3450002 A x s t)). Qed.
Lemma lem3450004 {A : Type'} (x : type684 A) (s : A -> Prop) : (term152 A x s) = (term148 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3450003 A x s t)). Qed.
Lemma lem3450005 {A : Type'} : (@ex (A -> Prop)) = (@ex (A -> Prop)).
Proof. exact (eq_refl (@ex (A -> Prop))). Qed.
Lemma lem3450006 {A : Type'} (x : type684 A) (s : A -> Prop) : (term153 A x s) = (term134 A x s).
Proof. exact (MK_COMB (@lem3450005 A) (@lem3450004 A x s)). Qed.
Lemma lem3450007 {A : Type'} (x : type684 A) : (term154 A x) = (term136 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3450006 A x s)). Qed.
Lemma lem3450008 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3450009 {A : Type'} (x : type684 A) : (term144 A x) = (term138 A x).
Proof. exact (MK_COMB (@lem3450008 A) (@lem3450007 A x)). Qed.
Lemma lem3450010 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3450011 {A : Type'} (x : type684 A) : (term155 A x) = (term156 A x).
Proof. exact (MK_COMB (@lem3450010) (@lem3450009 A x)). Qed.
Lemma lem3450012 {A : Type'} (x : type684 A) (s : A -> Prop) : (term147 A x s) = (term148 A x s).
Proof. exact (eq_refl (term147 A x s)). Qed.
Lemma lem3450013 {A : Type'} (t : type672 A) (s : A -> Prop) : (t s) = (t s).
Proof. exact (eq_refl (t s)). Qed.
Lemma lem3450014 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term157 A x t s) = (term158 A x t s).
Proof. exact (MK_COMB (@lem3450012 A x s) (@lem3450013 A t s)). Qed.
Lemma lem3450015 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term158 A x t s) = (term159 A x t s).
Proof. exact (eq_refl (term158 A x t s)). Qed.
Lemma lem3450016 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term157 A x t s) = (term159 A x t s).
Proof. exact (TRANS (@lem3450014 A x t s) (@lem3450015 A x t s)). Qed.
Lemma lem3450017 {A : Type'} (x : type684 A) (t : type672 A) : (term160 A x t) = (term161 A x t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3450016 A x t s)). Qed.
Lemma lem3450018 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3450019 {A : Type'} (x : type684 A) (t : type672 A) : (term162 A x t) = (term163 A x t).
Proof. exact (MK_COMB (@lem3450018 A) (@lem3450017 A x t)). Qed.
Lemma lem3450020 {A : Type'} (x : type684 A) : (term164 A x) = (term165 A x).
Proof. exact (fun_ext (fun t : type672 A => @lem3450019 A x t)). Qed.
Lemma lem3450021 {A : Type'} : (@ex ((A -> Prop) -> A -> Prop)) = (@ex ((A -> Prop) -> A -> Prop)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> Prop))). Qed.
Lemma lem3450022 {A : Type'} (x : type684 A) : (term145 A x) = (term166 A x).
Proof. exact (MK_COMB (@lem3450021 A) (@lem3450020 A x)). Qed.
Lemma lem3450023 {A : Type'} (x : type684 A) : ((term144 A x) = (term145 A x)) = ((term138 A x) = (term166 A x)).
Proof. exact (MK_COMB (@lem3450011 A x) (@lem3450022 A x)). Qed.
Lemma lem3450024 {A : Type'} (x : type684 A) : (term138 A x) = (term166 A x).
Proof. exact (EQ_MP (@lem3450023 A x) (@lem3449998 A x)). Qed.
Lemma lem3450025 {A : Type'} : (term140 A) = (term167 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3450024 A x)). Qed.
Lemma lem3450026 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3450027 {A : Type'} : (term141 A) = (term168 A).
Proof. exact (MK_COMB (@lem3450026 A) (@lem3450025 A)). Qed.
Lemma lem3450028 {A : Type'} : (term116 A) = (term168 A).
Proof. exact (TRANS (@lem3449994 A) (@lem3450027 A)). Qed.
Lemma lem3450030 {A : Type'} : (term4 A) = (term168 A).
Proof. exact (TRANS (@lem3449964 A) (@lem3450028 A)). Qed.
Lemma lem3450031 {A : Type'} : (term4 A) = (term168 A).
Proof. exact (TRANS (@lem3449816 A) (@lem3450030 A)). Qed.
Lemma lem3450032 {A : Type'} (h1 : term4 A) : term168 A.
Proof. exact (EQ_MP (@lem3450031 A) (@lem3449622 A h1)). Qed.
Lemma lem3450033 {A : Type'} (x : type684 A) (h1 : term166 A x) : term166 A x.
Proof. exact (h1). Qed.
Lemma lem3450034 {A : Type'} (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term163 A x t.
Proof. exact (h1). Qed.
Lemma lem3450035 {A : Type'} (P : type686 A) (h1 : term82 A P) : term82 A P.
Proof. exact (h1). Qed.
Lemma lem3450036 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term79 A P s.
Proof. exact (h1). Qed.
Lemma lem3450071 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term159 A x t s) = (term159 A x t s).
Proof. exact (eq_refl (term159 A x t s)). Qed.
Lemma lem3450072 {A : Type'} (x : type684 A) (t : type672 A) : (term161 A x t) = (term161 A x t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3450071 A x t s)). Qed.
Lemma lem3450073 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3450074 {A : Type'} (x : type684 A) (t : type672 A) : (term163 A x t) = (term163 A x t).
Proof. exact (MK_COMB (@lem3450073 A) (@lem3450072 A x t)). Qed.
Lemma lem3450075 {A : Type'} (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term163 A x t.
Proof. exact (EQ_MP (@lem3450074 A x t) (@lem3450034 A x t h1)). Qed.
Lemma lem3450080 {A : Type'} (P : type686 A) (s : A -> Prop) : (term51 A P s) = (term51 A P s).
Proof. exact (eq_refl (term51 A P s)). Qed.
Lemma lem3450095 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term38 A P a s) = (term38 A P a s).
Proof. exact (eq_refl (term38 A P a s)). Qed.
Lemma lem3450096 {A : Type'} (P : type686 A) (a : A) : (term40 A P a) = (term40 A P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3450095 A P a s)). Qed.
Lemma lem3450097 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3450098 {A : Type'} (P : type686 A) (a : A) : (term41 A P a) = (term41 A P a).
Proof. exact (MK_COMB (@lem3450097 A) (@lem3450096 A P a)). Qed.
Lemma lem3450099 {A : Type'} (P : type686 A) : (term42 A P) = (term42 A P).
Proof. exact (fun_ext (fun a : A => @lem3450098 A P a)). Qed.
Lemma lem3450100 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3450101 {A : Type'} (P : type686 A) : (term43 A P) = (term43 A P).
Proof. exact (MK_COMB (@lem3450100 A) (@lem3450099 A P)). Qed.
Lemma lem3450106 {A : Type'} (P : type686 A) : (term28 A P) = (term28 A P).
Proof. exact (eq_refl (term28 A P)). Qed.
Lemma lem3450107 {A : Type'} (P : type686 A) : (term44 A P) = (term44 A P).
Proof. exact (MK_COMB (@lem3450106 A P) (@lem3450101 A P)). Qed.
Lemma lem3450108 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3450109 {A : Type'} (P : type686 A) : (term55 A P) = (term55 A P).
Proof. exact (MK_COMB (@lem3450108) (@lem3450107 A P)). Qed.
Lemma lem3450110 {A : Type'} (P : type686 A) (s : A -> Prop) : (term79 A P s) = (term79 A P s).
Proof. exact (MK_COMB (@lem3450109 A P) (@lem3450080 A P s)). Qed.
Lemma lem3450111 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term79 A P s.
Proof. exact (EQ_MP (@lem3450110 A P s) (@lem3450036 A P s h1)). Qed.
Lemma lem3450113 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term44 A P.
Proof. exact (proj1 (@lem3450111 A P s h1)). Qed.
Lemma lem3450114 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term43 A P.
Proof. exact (proj2 (@lem3450113 A P s h1)). Qed.
Lemma lem3450133 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term159 A x t s) = (term169 A x t s).
Proof. exact (@lem19490 (s = (term170 A x t s)) (s = (@EMPTY A)) (term171 A x t s)). Qed.
Lemma lem3450134 {A : Type'} (x : type684 A) (t : type672 A) : (term161 A x t) = (term172 A x t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3450133 A x t s)). Qed.
Lemma lem3450135 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3450137 {A : Type'} (x : type684 A) (t : type672 A) : (term163 A x t) = (term173 A x t).
Proof. exact (MK_COMB (@lem3450135 A) (@lem3450134 A x t)). Qed.
Lemma lem3450138 {A : Type'} (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term173 A x t.
Proof. exact (EQ_MP (@lem3450137 A x t) (@lem3450075 A x t h1)). Qed.
Lemma lem3450154 {A : Type'} (P : type686 A) (a : A) (s : A -> Prop) : (term38 A P a s) = (term38 A P a s).
Proof. exact (eq_refl (term38 A P a s)). Qed.
Lemma lem3450155 {A : Type'} (P : type686 A) (a : A) : (term40 A P a) = (term40 A P a).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3450154 A P a s)). Qed.
Lemma lem3450156 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3450157 {A : Type'} (P : type686 A) (a : A) : (term41 A P a) = (term41 A P a).
Proof. exact (MK_COMB (@lem3450156 A) (@lem3450155 A P a)). Qed.
Lemma lem3450158 {A : Type'} (P : type686 A) : (term42 A P) = (term42 A P).
Proof. exact (fun_ext (fun a : A => @lem3450157 A P a)). Qed.
Lemma lem3450159 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3450161 {A : Type'} (P : type686 A) : (term43 A P) = (term43 A P).
Proof. exact (MK_COMB (@lem3450159 A) (@lem3450158 A P)). Qed.
Lemma lem3450162 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term43 A P.
Proof. exact (EQ_MP (@lem3450161 A P) (@lem3450114 A P s h1)). Qed.
Lemma lem3450163 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term174 A x t _36374.
Proof. exact (@lem3450138 A x t h1 _36374). Qed.
Lemma lem3450164 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term174 A x t _36374) = (term169 A x t _36374).
Proof. exact (eq_refl (term174 A x t _36374)). Qed.
Lemma lem3450165 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term169 A x t _36374.
Proof. exact (EQ_MP (@lem3450164 A x t _36374) (@lem3450163 A _36374 x t h1)). Qed.
Lemma lem3450166 {A : Type'} (_36375 : A) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term175 A P _36375.
Proof. exact (@lem3450162 A P s h1 _36375). Qed.
Lemma lem3450167 {A : Type'} (P : type686 A) (_36375 : A) : (term175 A P _36375) = (term41 A P _36375).
Proof. exact (eq_refl (term175 A P _36375)). Qed.
Lemma lem3450168 {A : Type'} (_36375 : A) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term41 A P _36375.
Proof. exact (EQ_MP (@lem3450167 A P _36375) (@lem3450166 A _36375 P s h1)). Qed.
Lemma lem3450169 {A : Type'} (_36375 : A) (_36376 : A -> Prop) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term176 A P _36375 _36376.
Proof. exact (@lem3450168 A _36375 P s h1 _36376). Qed.
Lemma lem3450170 {A : Type'} (P : type686 A) (_36375 : A) (_36376 : A -> Prop) : (term176 A P _36375 _36376) = (term38 A P _36375 _36376).
Proof. exact (eq_refl (term176 A P _36375 _36376)). Qed.
Lemma lem3450175 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term51 A P s.
Proof. exact (proj2 (@lem3450111 A P s h1)). Qed.
Lemma lem3450183 {A : Type'} (_36375 : A) (_36376 : A -> Prop) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term38 A P _36375 _36376.
Proof. exact (EQ_MP (@lem3450170 A P _36375 _36376) (@lem3450169 A _36375 _36376 P s h1)). Qed.
Lemma lem3450189 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term177 A x t _36374.
Proof. exact (proj1 (@lem3450165 A _36374 x t h1)). Qed.
Lemma lem3450195 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term178 A x t _36374.
Proof. exact (proj2 (@lem3450165 A _36374 x t h1)). Qed.
Lemma lem3450215 {A : Type'} (P : type686 A) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem3450216 {A : Type'} (_36381 : A -> Prop) (_36382 : A -> Prop) (h1 : _36381 = _36382) : _36381 = _36382.
Proof. exact (h1). Qed.
Lemma lem3450217 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) (h1 : _36381 = _36382) : (P _36381) = (P _36382).
Proof. exact (MK_COMB (@lem3450215 A P) (@lem3450216 A _36381 _36382 h1)). Qed.
Lemma lem3450219 (b : Prop) (a : Prop) : term179 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3450220 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : term180 A _36382 P _36381.
Proof. exact (@lem3450219 (P _36382) (P _36381)). Qed.
Lemma lem3450221 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) (h1 : _36381 = _36382) : term181 A _36382 P _36381.
Proof. exact (@lem3450220 A _36382 P _36381 (@lem3450217 A P _36381 _36382 h1)). Qed.
Lemma lem3450222 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : term182 A _36382 P _36381.
Proof. exact (fun h0 : _36381 = _36382 => @lem3450221 A P _36381 _36382 h0). Qed.
Lemma lem3450224 (a : Prop) (b : Prop) : (a -> b) = (term183 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3450225 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term182 A _36382 P _36381) = (term184 A _36382 P _36381).
Proof. exact (@lem3450224 (_36381 = _36382) (term181 A _36382 P _36381)). Qed.
Lemma lem3450226 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : term184 A _36382 P _36381.
Proof. exact (EQ_MP (@lem3450225 A _36382 P _36381) (@lem3450222 A _36382 P _36381)). Qed.
Lemma lem3450259 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term185 A x y z.
Proof. exact (@lem21385 (A -> Prop) x y z). Qed.
Lemma lem3450264 {A : Type'} (s : A -> Prop) (h1 : term186 A s) : term186 A s.
Proof. exact (h1). Qed.
Lemma lem3450265 {A : Type'} (s : A -> Prop) (h1 : term186 A s) : term187 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem3450264 A s h1). Qed.
Lemma lem3450267 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3450268 {A : Type'} (s : A -> Prop) : (term187 A s) = (term186 A s).
Proof. exact (@lem3450267 (s = (@EMPTY A))). Qed.
Lemma lem3450269 {A : Type'} (s : A -> Prop) (h1 : term186 A s) : term186 A s.
Proof. exact (EQ_MP (@lem3450268 A s) (@lem3450265 A s h1)). Qed.
Lemma lem3450284 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3450285 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term189 A x t _36374) = (term177 A x t _36374).
Proof. exact (@lem3450284 (_36374 = (@EMPTY A)) (_36374 = (term170 A x t _36374))). Qed.
Lemma lem3450295 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term190 A x t _36374) = (term190 A x t _36374).
Proof. exact (eq_refl (term190 A x t _36374)). Qed.
Lemma lem3450296 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : ((term177 A x t _36374) = (term189 A x t _36374)) = ((term177 A x t _36374) = (term177 A x t _36374)).
Proof. exact (MK_COMB (@lem3450295 A x t _36374) (@lem3450285 A x t _36374)). Qed.
Lemma lem3450298 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3450299 (x : Prop) : (x = x) = True.
Proof. exact (@lem3450298 Prop x). Qed.
Lemma lem3450300 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : ((term177 A x t _36374) = (term177 A x t _36374)) = True.
Proof. exact (@lem3450299 (term177 A x t _36374)). Qed.
Lemma lem3450301 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : ((term177 A x t _36374) = (term189 A x t _36374)) = True.
Proof. exact (TRANS (@lem3450296 A x t _36374) (@lem3450300 A x t _36374)). Qed.
Lemma lem3450302 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : True = ((term177 A x t _36374) = (term189 A x t _36374)).
Proof. exact (SYM (@lem3450301 A x t _36374)). Qed.
Lemma lem3450303 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term177 A x t _36374) = (term189 A x t _36374).
Proof. exact (EQ_MP (@lem3450302 A x t _36374) (@lem0)). Qed.
Lemma lem3450304 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term189 A x t _36374.
Proof. exact (EQ_MP (@lem3450303 A x t _36374) (@lem3450189 A _36374 x t h1)). Qed.
Lemma lem3450306 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3450309 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term189 A x t _36374) = (term192 A x t _36374).
Proof. exact (@lem3450306 (_36374 = (@EMPTY A)) (_36374 = (term170 A x t _36374))). Qed.
Lemma lem3450312 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term192 A x t _36374.
Proof. exact (EQ_MP (@lem3450309 A x t _36374) (@lem3450304 A _36374 x t h1)). Qed.
Lemma lem3450313 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term192 A x t _36374.
Proof. exact (@lem3450312 A _36374 x t h1). Qed.
Lemma lem3450314 {A : Type'} (s : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term192 A x t s.
Proof. exact (@lem3450313 A s x t h1). Qed.
Lemma lem3450317 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : s = (term170 A x t s).
Proof. exact (@lem3450314 A s x t h1 (@lem3450269 A s h2)). Qed.
Lemma lem3450318 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : term193 A x t s.
Proof. exact (fun h0 : term194 A x t s => @lem3450317 A x t s h1 h2). Qed.
Lemma lem3450320 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450321 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term193 A x t s) = (s = (term170 A x t s)).
Proof. exact (@lem3450320 (s = (term170 A x t s))). Qed.
Lemma lem3450322 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : s = (term170 A x t s).
Proof. exact (EQ_MP (@lem3450321 A x t s) (@lem3450318 A x t s h1 h2)). Qed.
Lemma lem3450324 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3450325 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3450324 A x). Qed.
Lemma lem3450326 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem3450325 A s). Qed.
Lemma lem3450327 {A : Type'} (s : A -> Prop) : term196 A s.
Proof. exact (fun h0 : term197 A s => @lem3450326 A s). Qed.
Lemma lem3450329 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450330 {A : Type'} (s : A -> Prop) : (term196 A s) = (s = s).
Proof. exact (@lem3450329 (s = s)). Qed.
Lemma lem3450331 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3450330 A s) (@lem3450327 A s)). Qed.
Lemma lem3450349 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3450350 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term198 A x y z) = (term199 A y x z).
Proof. exact (@lem3450349 (y = z) (term200 A x z)). Qed.
Lemma lem3450360 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term201 A x y) = (term201 A x y).
Proof. exact (eq_refl (term201 A x y)). Qed.
Lemma lem3450361 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term185 A x y z) = (term202 A y x z).
Proof. exact (MK_COMB (@lem3450360 A x y) (@lem3450350 A y x z)). Qed.
Lemma lem3450365 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3450366 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term202 A y x z) = (term204 A y x z).
Proof. exact (@lem3450365 (y = z) (term200 A x y) (term200 A x z)). Qed.
Lemma lem3450388 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term185 A x y z) = (term204 A y x z).
Proof. exact (TRANS (@lem3450361 A y x z) (@lem3450366 A y x z)). Qed.
Lemma lem3450389 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3450390 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term205 A x y z) = (term206 A y x z).
Proof. exact (MK_COMB (@lem3450389) (@lem3450388 A y x z)). Qed.
Lemma lem3450412 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term204 A y x z) = (term204 A y x z).
Proof. exact (eq_refl (term204 A y x z)). Qed.
Lemma lem3450413 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term185 A x y z) = (term204 A y x z)) = ((term204 A y x z) = (term204 A y x z)).
Proof. exact (MK_COMB (@lem3450390 A y x z) (@lem3450412 A y x z)). Qed.
Lemma lem3450415 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3450416 (x : Prop) : (x = x) = True.
Proof. exact (@lem3450415 Prop x). Qed.
Lemma lem3450417 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term204 A y x z) = (term204 A y x z)) = True.
Proof. exact (@lem3450416 (term204 A y x z)). Qed.
Lemma lem3450418 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : ((term185 A x y z) = (term204 A y x z)) = True.
Proof. exact (TRANS (@lem3450413 A y x z) (@lem3450417 A y x z)). Qed.
Lemma lem3450419 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : True = ((term185 A x y z) = (term204 A y x z)).
Proof. exact (SYM (@lem3450418 A y x z)). Qed.
Lemma lem3450420 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term185 A x y z) = (term204 A y x z).
Proof. exact (EQ_MP (@lem3450419 A y x z) (@lem0)). Qed.
Lemma lem3450421 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : term204 A y x z.
Proof. exact (EQ_MP (@lem3450420 A y x z) (@lem3450259 A x y z)). Qed.
Lemma lem3450423 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3450424 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term204 A y x z) = (term207 A x y z).
Proof. exact (@lem3450423 (term208 A y x z) (y = z)). Qed.
Lemma lem3450426 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3450427 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term211 A y x z) = (term212 A y x z).
Proof. exact (@lem3450426 (term200 A x y) (term200 A x z)). Qed.
Lemma lem3450429 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3450430 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term214 A x y) = (x = y).
Proof. exact (@lem3450429 (x = y)). Qed.
Lemma lem3450431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3450432 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term215 A x y) = (term216 A x y).
Proof. exact (MK_COMB (@lem3450431) (@lem3450430 A x y)). Qed.
Lemma lem3450434 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3450435 {A : Type'} (x : A -> Prop) (z : A -> Prop) : (term214 A x z) = (x = z).
Proof. exact (@lem3450434 (x = z)). Qed.
Lemma lem3450436 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term212 A y x z) = (term217 A y x z).
Proof. exact (MK_COMB (@lem3450432 A x y) (@lem3450435 A x z)). Qed.
Lemma lem3450437 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term211 A y x z) = (term217 A y x z).
Proof. exact (TRANS (@lem3450427 A y x z) (@lem3450436 A y x z)). Qed.
Lemma lem3450438 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3450439 {A : Type'} (y : A -> Prop) (x : A -> Prop) (z : A -> Prop) : (term218 A y x z) = (term219 A y x z).
Proof. exact (MK_COMB (@lem3450438) (@lem3450437 A y x z)). Qed.
Lemma lem3450440 {A : Type'} (y : A -> Prop) (z : A -> Prop) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem3450441 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term207 A x y z) = (term220 A x y z).
Proof. exact (MK_COMB (@lem3450439 A y x z) (@lem3450440 A y z)). Qed.
Lemma lem3450442 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : (term204 A y x z) = (term220 A x y z).
Proof. exact (TRANS (@lem3450424 A x y z) (@lem3450441 A x y z)). Qed.
Lemma lem3450444 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : term221 A x t s.
Proof. exact (conj (@lem3450322 A x t s h1 h2) (@lem3450331 A s)). Qed.
Lemma lem3450446 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term220 A x y z.
Proof. exact (EQ_MP (@lem3450442 A x y z) (@lem3450421 A y x z)). Qed.
Lemma lem3450447 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term220 A x y z.
Proof. exact (@lem3450446 A x y z). Qed.
Lemma lem3450448 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : term222 A x t s.
Proof. exact (@lem3450447 A s (term170 A x t s) s). Qed.
Lemma lem3450451 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : (term170 A x t s) = s.
Proof. exact (@lem3450448 A x t s (@lem3450444 A x t s h1 h2)). Qed.
Lemma lem3450452 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : term223 A x t s.
Proof. exact (fun h0 : term224 A x t s => @lem3450451 A x t s h1 h2). Qed.
Lemma lem3450454 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450455 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term223 A x t s) = ((term170 A x t s) = s).
Proof. exact (@lem3450454 ((term170 A x t s) = s)). Qed.
Lemma lem3450456 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term186 A s) : (term170 A x t s) = s.
Proof. exact (EQ_MP (@lem3450455 A x t s) (@lem3450452 A x t s h1 h2)). Qed.
Lemma lem3450459 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term51 A P s) : term51 A P s.
Proof. exact (h1). Qed.
Lemma lem3450460 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term51 A P s) : term225 A P s.
Proof. exact (fun h0 : P s => @lem3450459 A P s h1). Qed.
Lemma lem3450462 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3450463 {A : Type'} (P : type686 A) (s : A -> Prop) : (term225 A P s) = (term51 A P s).
Proof. exact (@lem3450462 (P s)). Qed.
Lemma lem3450464 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term51 A P s) : term51 A P s.
Proof. exact (EQ_MP (@lem3450463 A P s) (@lem3450460 A P s h1)). Qed.
Lemma lem3450470 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3450471 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term184 A _36382 P _36381) = (term226 A _36382 P _36381).
Proof. exact (@lem3450470 (P _36382) (term200 A _36381 _36382) (term51 A P _36381)). Qed.
Lemma lem3450485 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3450486 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term227 A _36382 P _36381) = (term228 A P _36381 _36382).
Proof. exact (@lem3450485 (term51 A P _36381) (term200 A _36381 _36382)). Qed.
Lemma lem3450494 {A : Type'} (P : type686 A) (_36382 : A -> Prop) : (term229 A P _36382) = (term229 A P _36382).
Proof. exact (eq_refl (term229 A P _36382)). Qed.
Lemma lem3450495 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term226 A _36382 P _36381) = (term230 A P _36381 _36382).
Proof. exact (MK_COMB (@lem3450494 A P _36382) (@lem3450486 A P _36381 _36382)). Qed.
Lemma lem3450506 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term184 A _36382 P _36381) = (term230 A P _36381 _36382).
Proof. exact (TRANS (@lem3450471 A _36382 P _36381) (@lem3450495 A P _36381 _36382)). Qed.
Lemma lem3450507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3450508 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term231 A _36382 P _36381) = (term232 A P _36381 _36382).
Proof. exact (MK_COMB (@lem3450507) (@lem3450506 A P _36381 _36382)). Qed.
Lemma lem3450522 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3450523 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term233 A _36381 P _36382) = (term234 A P _36381 _36382).
Proof. exact (@lem3450522 (P _36382) (term200 A _36381 _36382)). Qed.
Lemma lem3450531 {A : Type'} (P : type686 A) (_36381 : A -> Prop) : (term235 A P _36381) = (term235 A P _36381).
Proof. exact (eq_refl (term235 A P _36381)). Qed.
Lemma lem3450532 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term236 A _36381 P _36382) = (term237 A P _36381 _36382).
Proof. exact (MK_COMB (@lem3450531 A P _36381) (@lem3450523 A P _36381 _36382)). Qed.
Lemma lem3450536 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3450537 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term237 A P _36381 _36382) = (term230 A P _36381 _36382).
Proof. exact (@lem3450536 (P _36382) (term51 A P _36381) (term200 A _36381 _36382)). Qed.
Lemma lem3450555 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term236 A _36381 P _36382) = (term230 A P _36381 _36382).
Proof. exact (TRANS (@lem3450532 A P _36381 _36382) (@lem3450537 A P _36381 _36382)). Qed.
Lemma lem3450556 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : ((term184 A _36382 P _36381) = (term236 A _36381 P _36382)) = ((term230 A P _36381 _36382) = (term230 A P _36381 _36382)).
Proof. exact (MK_COMB (@lem3450508 A P _36381 _36382) (@lem3450555 A P _36381 _36382)). Qed.
Lemma lem3450558 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3450559 (x : Prop) : (x = x) = True.
Proof. exact (@lem3450558 Prop x). Qed.
Lemma lem3450560 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : ((term230 A P _36381 _36382) = (term230 A P _36381 _36382)) = True.
Proof. exact (@lem3450559 (term230 A P _36381 _36382)). Qed.
Lemma lem3450561 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : ((term184 A _36382 P _36381) = (term236 A _36381 P _36382)) = True.
Proof. exact (TRANS (@lem3450556 A P _36381 _36382) (@lem3450560 A P _36381 _36382)). Qed.
Lemma lem3450562 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : True = ((term184 A _36382 P _36381) = (term236 A _36381 P _36382)).
Proof. exact (SYM (@lem3450561 A _36381 P _36382)). Qed.
Lemma lem3450563 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term184 A _36382 P _36381) = (term236 A _36381 P _36382).
Proof. exact (EQ_MP (@lem3450562 A _36381 P _36382) (@lem0)). Qed.
Lemma lem3450564 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : term236 A _36381 P _36382.
Proof. exact (EQ_MP (@lem3450563 A _36381 P _36382) (@lem3450226 A _36382 P _36381)). Qed.
Lemma lem3450566 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3450567 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term236 A _36381 P _36382) = (term238 A _36382 P _36381).
Proof. exact (@lem3450566 (term233 A _36381 P _36382) (term51 A P _36381)). Qed.
Lemma lem3450569 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3450570 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term239 A _36381 P _36382) = (term240 A _36381 P _36382).
Proof. exact (@lem3450569 (term200 A _36381 _36382) (P _36382)). Qed.
Lemma lem3450572 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3450573 {A : Type'} (_36381 : A -> Prop) (_36382 : A -> Prop) : (term214 A _36381 _36382) = (_36381 = _36382).
Proof. exact (@lem3450572 (_36381 = _36382)). Qed.
Lemma lem3450574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3450575 {A : Type'} (_36381 : A -> Prop) (_36382 : A -> Prop) : (term215 A _36381 _36382) = (term216 A _36381 _36382).
Proof. exact (MK_COMB (@lem3450574) (@lem3450573 A _36381 _36382)). Qed.
Lemma lem3450576 {A : Type'} (P : type686 A) (_36382 : A -> Prop) : (term51 A P _36382) = (term51 A P _36382).
Proof. exact (eq_refl (term51 A P _36382)). Qed.
Lemma lem3450577 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term240 A _36381 P _36382) = (term241 A _36381 P _36382).
Proof. exact (MK_COMB (@lem3450575 A _36381 _36382) (@lem3450576 A P _36382)). Qed.
Lemma lem3450578 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term239 A _36381 P _36382) = (term241 A _36381 P _36382).
Proof. exact (TRANS (@lem3450570 A _36381 P _36382) (@lem3450577 A _36381 P _36382)). Qed.
Lemma lem3450579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3450580 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term242 A _36381 P _36382) = (term243 A _36381 P _36382).
Proof. exact (MK_COMB (@lem3450579) (@lem3450578 A _36381 P _36382)). Qed.
Lemma lem3450581 {A : Type'} (P : type686 A) (_36381 : A -> Prop) : (term51 A P _36381) = (term51 A P _36381).
Proof. exact (eq_refl (term51 A P _36381)). Qed.
Lemma lem3450582 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term238 A _36382 P _36381) = (term244 A _36382 P _36381).
Proof. exact (MK_COMB (@lem3450580 A _36381 P _36382) (@lem3450581 A P _36381)). Qed.
Lemma lem3450583 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term236 A _36381 P _36382) = (term244 A _36382 P _36381).
Proof. exact (TRANS (@lem3450567 A _36382 P _36381) (@lem3450582 A _36382 P _36381)). Qed.
Lemma lem3450585 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) : term245 A x t P s.
Proof. exact (conj (@lem3450456 A x t s h1 h3) (@lem3450464 A P s h2)). Qed.
Lemma lem3450587 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : term244 A _36382 P _36381.
Proof. exact (EQ_MP (@lem3450583 A _36382 P _36381) (@lem3450564 A _36381 P _36382)). Qed.
Lemma lem3450588 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : term244 A _36382 P _36381.
Proof. exact (@lem3450587 A _36382 P _36381). Qed.
Lemma lem3450589 {A : Type'} (P : type686 A) (x : type684 A) (t : type672 A) (s : A -> Prop) : term246 A P x t s.
Proof. exact (@lem3450588 A s P (term170 A x t s)). Qed.
Lemma lem3450592 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) : term247 A P x t s.
Proof. exact (@lem3450589 A P x t s (@lem3450585 A x t P s h1 h2 h3)). Qed.
Lemma lem3450593 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) : term248 A P x t s.
Proof. exact (fun h0 : term249 A P x t s => @lem3450592 A x t P s h1 h2 h3). Qed.
Lemma lem3450595 (p : Prop) : (term188 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3450596 {A : Type'} (P : type686 A) (x : type684 A) (t : type672 A) (s : A -> Prop) : (term248 A P x t s) = (term247 A P x t s).
Proof. exact (@lem3450595 (term249 A P x t s)). Qed.
Lemma lem3450597 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) : term247 A P x t s.
Proof. exact (EQ_MP (@lem3450596 A P x t s) (@lem3450593 A x t P s h1 h2 h3)). Qed.
Lemma lem3450599 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3450602 {A : Type'} (P : type686 A) (_36375 : A) (_36376 : A -> Prop) : (term38 A P _36375 _36376) = (term250 A P _36375 _36376).
Proof. exact (@lem3450599 (term34 A P _36375 _36376) (@IN A _36375 _36376)). Qed.
Lemma lem3450605 {A : Type'} (_36375 : A) (_36376 : A -> Prop) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term250 A P _36375 _36376.
Proof. exact (EQ_MP (@lem3450602 A P _36375 _36376) (@lem3450183 A _36375 _36376 P s h1)). Qed.
Lemma lem3450606 {A : Type'} (_36375 : A) (_36376 : A -> Prop) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term250 A P _36375 _36376.
Proof. exact (@lem3450605 A _36375 _36376 P s h1). Qed.
Lemma lem3450607 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term251 A P x t s.
Proof. exact (@lem3450606 A (x s) (t s) P s h1). Qed.
Lemma lem3450610 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) (h4 : term79 A P s) : term252 A x t s.
Proof. exact (@lem3450607 A x t P s h4 (@lem3450597 A x t P s h1 h2 h3)). Qed.
Lemma lem3450611 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) (h4 : term79 A P s) : term253 A x t s.
Proof. exact (fun h0 : term171 A x t s => @lem3450610 A x t P s h1 h2 h3 h4). Qed.
Lemma lem3450613 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450614 {A : Type'} (x : type684 A) (t : type672 A) (s : A -> Prop) : (term253 A x t s) = (term252 A x t s).
Proof. exact (@lem3450613 (term252 A x t s)). Qed.
Lemma lem3450615 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) (h4 : term79 A P s) : term252 A x t s.
Proof. exact (EQ_MP (@lem3450614 A x t s) (@lem3450611 A x t P s h1 h2 h3 h4)). Qed.
Lemma lem3450617 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3450618 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term178 A x t _36374) = (term254 A x t _36374).
Proof. exact (@lem3450617 (term171 A x t _36374) (_36374 = (@EMPTY A))). Qed.
Lemma lem3450620 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3450621 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term255 A x t _36374) = (term252 A x t _36374).
Proof. exact (@lem3450620 (term252 A x t _36374)). Qed.
Lemma lem3450622 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3450623 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term256 A x t _36374) = (term257 A x t _36374).
Proof. exact (MK_COMB (@lem3450622) (@lem3450621 A x t _36374)). Qed.
Lemma lem3450624 {A : Type'} (_36374 : A -> Prop) : (_36374 = (@EMPTY A)) = (_36374 = (@EMPTY A)).
Proof. exact (eq_refl (_36374 = (@EMPTY A))). Qed.
Lemma lem3450625 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term254 A x t _36374) = (term258 A x t _36374).
Proof. exact (MK_COMB (@lem3450623 A x t _36374) (@lem3450624 A _36374)). Qed.
Lemma lem3450626 {A : Type'} (x : type684 A) (t : type672 A) (_36374 : A -> Prop) : (term178 A x t _36374) = (term258 A x t _36374).
Proof. exact (TRANS (@lem3450618 A x t _36374) (@lem3450625 A x t _36374)). Qed.
Lemma lem3450629 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term258 A x t _36374.
Proof. exact (EQ_MP (@lem3450626 A x t _36374) (@lem3450195 A _36374 x t h1)). Qed.
Lemma lem3450630 {A : Type'} (_36374 : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term258 A x t _36374.
Proof. exact (@lem3450629 A _36374 x t h1). Qed.
Lemma lem3450631 {A : Type'} (s : A -> Prop) (x : type684 A) (t : type672 A) (h1 : term163 A x t) : term258 A x t s.
Proof. exact (@lem3450630 A s x t h1). Qed.
Lemma lem3450634 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term186 A s) (h4 : term79 A P s) : s = (@EMPTY A).
Proof. exact (@lem3450631 A s x t h1 (@lem3450615 A x t P s h1 h2 h3 h4)). Qed.
Lemma lem3450635 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : term259 A s.
Proof. exact (fun h0 : term186 A s => @lem3450634 A x t P s h1 h2 h0 h3). Qed.
Lemma lem3450637 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450638 {A : Type'} (s : A -> Prop) : (term259 A s) = (s = (@EMPTY A)).
Proof. exact (@lem3450637 (s = (@EMPTY A))). Qed.
Lemma lem3450639 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem3450638 A s) (@lem3450635 A x t P s h1 h2 h3)). Qed.
Lemma lem3450641 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem21386 (A -> Prop) x). Qed.
Lemma lem3450642 {A : Type'} (x : A -> Prop) : x = x.
Proof. exact (@lem3450641 A x). Qed.
Lemma lem3450643 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (@lem3450642 A s). Qed.
Lemma lem3450644 {A : Type'} (s : A -> Prop) : term196 A s.
Proof. exact (fun h0 : term197 A s => @lem3450643 A s). Qed.
Lemma lem3450646 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450647 {A : Type'} (s : A -> Prop) : (term196 A s) = (s = s).
Proof. exact (@lem3450646 (s = s)). Qed.
Lemma lem3450648 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (EQ_MP (@lem3450647 A s) (@lem3450644 A s)). Qed.
Lemma lem3450649 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : term260 A s.
Proof. exact (conj (@lem3450639 A x t P s h1 h2 h3) (@lem3450648 A s)). Qed.
Lemma lem3450651 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term220 A x y z.
Proof. exact (EQ_MP (@lem3450442 A x y z) (@lem3450421 A y x z)). Qed.
Lemma lem3450652 {A : Type'} (x : A -> Prop) (y : A -> Prop) (z : A -> Prop) : term220 A x y z.
Proof. exact (@lem3450651 A x y z). Qed.
Lemma lem3450653 {A : Type'} (s : A -> Prop) : term261 A s.
Proof. exact (@lem3450652 A s (@EMPTY A) s). Qed.
Lemma lem3450656 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : (@EMPTY A) = s.
Proof. exact (@lem3450653 A s (@lem3450649 A x t P s h1 h2 h3)). Qed.
Lemma lem3450657 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : term262 A s.
Proof. exact (fun h0 : term263 A s => @lem3450656 A x t P s h1 h2 h3). Qed.
Lemma lem3450659 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450660 {A : Type'} (s : A -> Prop) : (term262 A s) = ((@EMPTY A) = s).
Proof. exact (@lem3450659 ((@EMPTY A) = s)). Qed.
Lemma lem3450661 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : (@EMPTY A) = s.
Proof. exact (EQ_MP (@lem3450660 A s) (@lem3450657 A x t P s h1 h2 h3)). Qed.
Lemma lem3450663 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : P (@EMPTY A).
Proof. exact (proj1 (@lem3450113 A P s h1)). Qed.
Lemma lem3450664 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term264 A P.
Proof. exact (fun h0 : term265 A P => @lem3450663 A P s h1). Qed.
Lemma lem3450666 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450667 {A : Type'} (P : type686 A) : (term264 A P) = (P (@EMPTY A)).
Proof. exact (@lem3450666 (P (@EMPTY A))). Qed.
Lemma lem3450668 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : P (@EMPTY A).
Proof. exact (EQ_MP (@lem3450667 A P) (@lem3450664 A P s h1)). Qed.
Lemma lem3450674 (q : Prop) (p : Prop) (r : Prop) : (term203 p q r) = (term203 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3450675 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term184 A _36382 P _36381) = (term226 A _36382 P _36381).
Proof. exact (@lem3450674 (P _36382) (term200 A _36381 _36382) (term51 A P _36381)). Qed.
Lemma lem3450689 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3450690 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term227 A _36382 P _36381) = (term228 A P _36381 _36382).
Proof. exact (@lem3450689 (term51 A P _36381) (term200 A _36381 _36382)). Qed.
Lemma lem3450698 {A : Type'} (P : type686 A) (_36382 : A -> Prop) : (term229 A P _36382) = (term229 A P _36382).
Proof. exact (eq_refl (term229 A P _36382)). Qed.
Lemma lem3450699 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term226 A _36382 P _36381) = (term230 A P _36381 _36382).
Proof. exact (MK_COMB (@lem3450698 A P _36382) (@lem3450690 A P _36381 _36382)). Qed.
Lemma lem3450710 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term184 A _36382 P _36381) = (term230 A P _36381 _36382).
Proof. exact (TRANS (@lem3450675 A _36382 P _36381) (@lem3450699 A P _36381 _36382)). Qed.
Lemma lem3450711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3450712 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term231 A _36382 P _36381) = (term232 A P _36381 _36382).
Proof. exact (MK_COMB (@lem3450711) (@lem3450710 A P _36381 _36382)). Qed.
Lemma lem3450726 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3450727 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term227 A _36382 P _36381) = (term228 A P _36381 _36382).
Proof. exact (@lem3450726 (term51 A P _36381) (term200 A _36381 _36382)). Qed.
Lemma lem3450735 {A : Type'} (P : type686 A) (_36382 : A -> Prop) : (term229 A P _36382) = (term229 A P _36382).
Proof. exact (eq_refl (term229 A P _36382)). Qed.
Lemma lem3450736 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : (term226 A _36382 P _36381) = (term230 A P _36381 _36382).
Proof. exact (MK_COMB (@lem3450735 A P _36382) (@lem3450727 A P _36381 _36382)). Qed.
Lemma lem3450747 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : ((term184 A _36382 P _36381) = (term226 A _36382 P _36381)) = ((term230 A P _36381 _36382) = (term230 A P _36381 _36382)).
Proof. exact (MK_COMB (@lem3450712 A P _36381 _36382) (@lem3450736 A P _36381 _36382)). Qed.
Lemma lem3450749 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3450750 (x : Prop) : (x = x) = True.
Proof. exact (@lem3450749 Prop x). Qed.
Lemma lem3450751 {A : Type'} (P : type686 A) (_36381 : A -> Prop) (_36382 : A -> Prop) : ((term230 A P _36381 _36382) = (term230 A P _36381 _36382)) = True.
Proof. exact (@lem3450750 (term230 A P _36381 _36382)). Qed.
Lemma lem3450752 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : ((term184 A _36382 P _36381) = (term226 A _36382 P _36381)) = True.
Proof. exact (TRANS (@lem3450747 A P _36381 _36382) (@lem3450751 A P _36381 _36382)). Qed.
Lemma lem3450753 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : True = ((term184 A _36382 P _36381) = (term226 A _36382 P _36381)).
Proof. exact (SYM (@lem3450752 A _36382 P _36381)). Qed.
Lemma lem3450754 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term184 A _36382 P _36381) = (term226 A _36382 P _36381).
Proof. exact (EQ_MP (@lem3450753 A _36382 P _36381) (@lem0)). Qed.
Lemma lem3450755 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : term226 A _36382 P _36381.
Proof. exact (EQ_MP (@lem3450754 A _36382 P _36381) (@lem3450226 A _36382 P _36381)). Qed.
Lemma lem3450757 (b : Prop) (a : Prop) : (a \/ b) = (term191 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3450758 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term226 A _36382 P _36381) = (term266 A _36381 P _36382).
Proof. exact (@lem3450757 (term227 A _36382 P _36381) (P _36382)). Qed.
Lemma lem3450760 (a : Prop) (b : Prop) : (term209 a b) = (term210 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3450761 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term267 A _36382 P _36381) = (term268 A _36382 P _36381).
Proof. exact (@lem3450760 (term200 A _36381 _36382) (term51 A P _36381)). Qed.
Lemma lem3450763 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3450764 {A : Type'} (_36381 : A -> Prop) (_36382 : A -> Prop) : (term214 A _36381 _36382) = (_36381 = _36382).
Proof. exact (@lem3450763 (_36381 = _36382)). Qed.
Lemma lem3450765 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3450766 {A : Type'} (_36381 : A -> Prop) (_36382 : A -> Prop) : (term215 A _36381 _36382) = (term216 A _36381 _36382).
Proof. exact (MK_COMB (@lem3450765) (@lem3450764 A _36381 _36382)). Qed.
Lemma lem3450768 (a : Prop) : (term213 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3450769 {A : Type'} (P : type686 A) (_36381 : A -> Prop) : (term269 A P _36381) = (P _36381).
Proof. exact (@lem3450768 (P _36381)). Qed.
Lemma lem3450770 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term268 A _36382 P _36381) = (term270 A _36382 P _36381).
Proof. exact (MK_COMB (@lem3450766 A _36381 _36382) (@lem3450769 A P _36381)). Qed.
Lemma lem3450771 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term267 A _36382 P _36381) = (term270 A _36382 P _36381).
Proof. exact (TRANS (@lem3450761 A _36382 P _36381) (@lem3450770 A _36382 P _36381)). Qed.
Lemma lem3450772 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3450773 {A : Type'} (_36382 : A -> Prop) (P : type686 A) (_36381 : A -> Prop) : (term271 A _36382 P _36381) = (term272 A _36382 P _36381).
Proof. exact (MK_COMB (@lem3450772) (@lem3450771 A _36382 P _36381)). Qed.
Lemma lem3450774 {A : Type'} (P : type686 A) (_36382 : A -> Prop) : (P _36382) = (P _36382).
Proof. exact (eq_refl (P _36382)). Qed.
Lemma lem3450775 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term266 A _36381 P _36382) = (term273 A _36381 P _36382).
Proof. exact (MK_COMB (@lem3450773 A _36382 P _36381) (@lem3450774 A P _36382)). Qed.
Lemma lem3450776 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : (term226 A _36382 P _36381) = (term273 A _36381 P _36382).
Proof. exact (TRANS (@lem3450758 A _36381 P _36382) (@lem3450775 A _36381 P _36382)). Qed.
Lemma lem3450778 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : term274 A s P.
Proof. exact (conj (@lem3450661 A x t P s h1 h2 h3) (@lem3450668 A P s h3)). Qed.
Lemma lem3450780 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : term273 A _36381 P _36382.
Proof. exact (EQ_MP (@lem3450776 A _36381 P _36382) (@lem3450755 A _36382 P _36381)). Qed.
Lemma lem3450781 {A : Type'} (_36381 : A -> Prop) (P : type686 A) (_36382 : A -> Prop) : term273 A _36381 P _36382.
Proof. exact (@lem3450780 A _36381 P _36382). Qed.
Lemma lem3450782 {A : Type'} (P : type686 A) (s : A -> Prop) : term275 A P s.
Proof. exact (@lem3450781 A (@EMPTY A) P s). Qed.
Lemma lem3450785 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term51 A P s) (h3 : term79 A P s) : P s.
Proof. exact (@lem3450782 A P s (@lem3450778 A x t P s h1 h2 h3)). Qed.
Lemma lem3450786 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : term276 A P s.
Proof. exact (fun h0 : term51 A P s => @lem3450785 A x t P s h1 h0 h2). Qed.
Lemma lem3450788 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450789 {A : Type'} (P : type686 A) (s : A -> Prop) : (term276 A P s) = (P s).
Proof. exact (@lem3450788 (P s)). Qed.
Lemma lem3450790 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : P s.
Proof. exact (EQ_MP (@lem3450789 A P s) (@lem3450786 A x t P s h1 h2)). Qed.
Lemma lem3450793 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3450795 {A : Type'} (P : type686 A) (s : A -> Prop) : (term51 A P s) = (term277 A P s).
Proof. exact (@lem3450793 (P s)). Qed.
Lemma lem3450798 {A : Type'} (P : type686 A) (s : A -> Prop) (h1 : term79 A P s) : term277 A P s.
Proof. exact (EQ_MP (@lem3450795 A P s) (@lem3450175 A P s h1)). Qed.
Lemma lem3450801 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : False.
Proof. exact (@lem3450798 A P s h2 (@lem3450790 A x t P s h1 h2)). Qed.
Lemma lem3450802 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : term278.
Proof. exact (fun h0 : ~ False => @lem3450801 A x t P s h1 h2). Qed.
Lemma lem3450804 (p : Prop) : (term195 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3450805 : term278 = False.
Proof. exact (@lem3450804 False). Qed.
Lemma lem3450806 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : False.
Proof. exact (EQ_MP (@lem3450805) (@lem3450802 A x t P s h1 h2)). Qed.
Lemma lem3450807 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : (term79 A P s) = False.
Proof. exact (prop_ext (fun h3 : term79 A P s => @lem3450806 A x t P s h1 h2) (fun h3 : False => @lem3450111 A P s h2)). Qed.
Lemma lem3450808 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : False.
Proof. exact (EQ_MP (@lem3450807 A x t P s h1 h2) (@lem3450111 A P s h2)). Qed.
Lemma lem3450809 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : (term163 A x t) = False.
Proof. exact (prop_ext (fun h3 : term163 A x t => @lem3450808 A x t P s h1 h2) (fun h3 : False => @lem3450075 A x t h1)). Qed.
Lemma lem3450810 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (s : A -> Prop) (h1 : term163 A x t) (h2 : term79 A P s) : False.
Proof. exact (EQ_MP (@lem3450809 A x t P s h1 h2) (@lem3450075 A x t h1)). Qed.
Lemma lem3450811 {A : Type'} (x : type684 A) (t : type672 A) (P : type686 A) (h1 : term163 A x t) (h2 : term82 A P) : False.
Proof. exact (ex_elim (@lem3450035 A P h2) (fun s : A -> Prop => fun h0 : term81 A P s => @lem3450810 A x t P s h1 h0)). Qed.
Lemma lem3450812 {A : Type'} (x : type684 A) (t : type672 A) (h1 : term163 A x t) (h2 : term3 A) : False.
Proof. exact (ex_elim (@lem3449798 A h2) (fun P : type686 A => fun h0 : term83 A P => @lem3450811 A x t P h1 h0)). Qed.
Lemma lem3450813 {A : Type'} (x : type684 A) (h1 : term166 A x) (h2 : term3 A) : False.
Proof. exact (ex_elim (@lem3450033 A x h1) (fun t : type672 A => fun h0 : term165 A x t => @lem3450812 A x t h0 h2)). Qed.
Lemma lem3450814 {A : Type'} (h1 : term4 A) (h2 : term3 A) : False.
Proof. exact (ex_elim (@lem3450032 A h1) (fun x : type684 A => fun h0 : term167 A x => @lem3450813 A x h0 h2)). Qed.
Lemma lem3450815 {A : Type'} (h1 : term3 A) : term9 A.
Proof. exact (fun h0 : term4 A => @lem3450814 A h0 h1). Qed.
Lemma lem3450816 {A : Type'} : (term9 A) = (term10 A).
Proof. exact (@lem69 (term4 A)). Qed.
Lemma lem3450817 {A : Type'} (h1 : term3 A) : term10 A.
Proof. exact (EQ_MP (@lem3450816 A) (@lem3450815 A h1)). Qed.
Lemma lem3450818 {A : Type'} : term12 A.
Proof. exact (fun h0 : term3 A => @lem3450817 A h0). Qed.
Lemma lem3450819 {A : Type'} : term5 A.
Proof. exact (EQ_MP (@lem3449620 A) (@lem3450818 A)). Qed.
Lemma lem3450821 {A : Type'} : term5 A.
Proof. exact (@lem3449369 A (@lem3450819 A)). Qed.
Lemma lem3450822 {A : Type'} (h1 : term3 A) : term9 A.
Proof. exact (@lem3450821 A (@lem3449350 A h1)). Qed.
Lemma lem3450823 {A : Type'} (h1 : term3 A) : False.
Proof. exact (@lem3450822 A h1 (@lem3449351 A)). Qed.
Lemma lem3450824 {A : Type'} (h1 : term3 A) : (term3 A) = False.
Proof. exact (prop_ext (fun h2 : term3 A => @lem3450823 A h1) (fun h2 : False => @lem3449350 A h1)). Qed.
Lemma lem3450825 {A : Type'} (h1 : term3 A) : False.
Proof. exact (EQ_MP (@lem3450824 A h1) (@lem3449350 A h1)). Qed.
Lemma lem3450826 {A : Type'} : term2 A.
Proof. exact (fun h0 : term3 A => @lem3450825 A h0). Qed.
Lemma lem3450827 {A : Type'} : term1 A.
Proof. exact (EQ_MP (@lem3449349 A) (@lem3450826 A)). Qed.
