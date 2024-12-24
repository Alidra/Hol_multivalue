Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import POLYNOMIAL_FUNCTION_NEG_term_abbrevs.
Require Import ETA_AX_spec.
Require Import POLYNOMIAL_FUNCTION_LMUL_spec.
Require Import REAL_MUL_LNEG_spec.
Require Import REAL_NEG_NEG_spec.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1823_spec.
Require Import thm32_spec.
Lemma lem7567594 (x : real) : term0 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem7567595 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem7567597 {A B : Type'} (t : A -> B) : term2 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem7567598 {A B : Type'} (t : A -> B) : (term2 A B t) = ((term3 A B t) = t).
Proof. exact (eq_refl (term2 A B t)). Qed.
Lemma lem7567599 {A B : Type'} (t : A -> B) : (term3 A B t) = t.
Proof. exact (EQ_MP (@lem7567598 A B t) (@lem7567597 A B t)). Qed.
Lemma lem7567600 (x : real) : term4 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem7567601 (x : real) : (term4 x) = ((term5 x) = x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem7567603 (x : real) : term6 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem7567604 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem7567605 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem7567604 x) (@lem7567603 x)). Qed.
Lemma lem7567606 (x : real) (y : real) : term8 x y.
Proof. exact (@lem7567605 x y). Qed.
Lemma lem7567607 (x : real) (y : real) : (term8 x y) = ((term9 x y) = (term10 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem7567609 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem7567610 (p : real -> real) (h1 : term11) : term12 p.
Proof. exact (@lem7567609 h1 p). Qed.
Lemma lem7567611 (p : real -> real) : (term12 p) = (term13 p).
Proof. exact (eq_refl (term12 p)). Qed.
Lemma lem7567612 (p : real -> real) (h1 : term11) : term13 p.
Proof. exact (EQ_MP (@lem7567611 p) (@lem7567610 p h1)). Qed.
Lemma lem7567613 (p : real -> real) (c : real) (h1 : term11) : term14 p c.
Proof. exact (@lem7567612 p h1 c). Qed.
Lemma lem7567614 (c : real) (p : real -> real) : (term14 p c) = (term15 c p).
Proof. exact (eq_refl (term14 p c)). Qed.
Lemma lem7567615 (c : real) (p : real -> real) (h1 : term11) : term15 c p.
Proof. exact (EQ_MP (@lem7567614 c p) (@lem7567613 p c h1)). Qed.
Lemma lem7567616 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7567617 (c : real) (p : real -> real) (h1 : term11) (h2 : polynomial_function p) : term16 c p.
Proof. exact (@lem7567615 c p h1 (@lem7567616 p h2)). Qed.
Lemma lem7567618 (p : real -> real) (h1 : term11) (h2 : polynomial_function p) : term17 p.
Proof. exact (fun c : real => @lem7567617 c p h1 h2). Qed.
Lemma lem7567619 (p : real -> real) (h1 : term11) : term18 p.
Proof. exact (fun h0 : polynomial_function p => @lem7567618 p h1 h0). Qed.
Lemma lem7567620 (h1 : term11) : term19.
Proof. exact (fun p : real -> real => @lem7567619 p h1). Qed.
Lemma lem7567621 : term20.
Proof. exact (fun h0 : term11 => @lem7567620 h0). Qed.
Lemma lem7567622 : term19.
Proof. exact (@lem7567621 (@lem7567525)). Qed.
Lemma lem7567623 (p : real -> real) : term21 p.
Proof. exact (@lem7567622 p). Qed.
Lemma lem7567624 (p : real -> real) : (term21 p) = (term18 p).
Proof. exact (eq_refl (term21 p)). Qed.
Lemma lem7567626 (p : real -> real) (h1 : term22 p) : term22 p.
Proof. exact (h1). Qed.
Lemma lem7567628 (p : real -> real) : term18 p.
Proof. exact (EQ_MP (@lem7567624 p) (@lem7567623 p)). Qed.
Lemma lem7567629 (p : real -> real) : term23 p.
Proof. exact (@lem7567628 (term24 p)). Qed.
Lemma lem7567630 (p : real -> real) (h1 : term22 p) : term25 p.
Proof. exact (@lem7567629 p (@lem7567626 p h1)). Qed.
Lemma lem7567631 (p : real -> real) (h1 : term22 p) : term26 p.
Proof. exact (@lem7567630 p h1 term27). Qed.
Lemma lem7567632 (p : real -> real) : (term26 p) = (term28 p).
Proof. exact (eq_refl (term26 p)). Qed.
Lemma lem7567633 (p : real -> real) (h1 : term22 p) : term28 p.
Proof. exact (EQ_MP (@lem7567632 p) (@lem7567631 p h1)). Qed.
Lemma lem7567634 (p : real -> real) (h1 : polynomial_function p) : polynomial_function p.
Proof. exact (h1). Qed.
Lemma lem7567636 (p : real -> real) : term18 p.
Proof. exact (EQ_MP (@lem7567624 p) (@lem7567623 p)). Qed.
Lemma lem7567637 (p : real -> real) (h1 : polynomial_function p) : term17 p.
Proof. exact (@lem7567636 p (@lem7567634 p h1)). Qed.
Lemma lem7567638 (p : real -> real) (h1 : polynomial_function p) : term29 p.
Proof. exact (@lem7567637 p h1 term27). Qed.
Lemma lem7567639 (p : real -> real) : (term29 p) = (term30 p).
Proof. exact (eq_refl (term29 p)). Qed.
Lemma lem7567640 (p : real -> real) (h1 : polynomial_function p) : term30 p.
Proof. exact (EQ_MP (@lem7567639 p) (@lem7567638 p h1)). Qed.
Lemma lem7567644 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem7567607 x y) (@lem7567606 x y)). Qed.
Lemma lem7567645 (p : real -> real) (x : real) : (term31 p x) = (term32 p x).
Proof. exact (@lem7567644 term33 (term34 p x)). Qed.
Lemma lem7567647 (x : real) : (term5 x) = x.
Proof. exact (EQ_MP (@lem7567601 x) (@lem7567600 x)). Qed.
Lemma lem7567648 (p : real -> real) (x : real) : (term35 p x) = (term34 p x).
Proof. exact (@lem7567647 (term34 p x)). Qed.
Lemma lem7567650 {A B : Type'} (f : A -> B) (y : A) : (term36 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7567651 (f : real -> real) (y : real) : (term37 f y) = (f y).
Proof. exact (@lem7567650 real real f y). Qed.
Lemma lem7567652 (p : real -> real) (x : real) : (term38 p x) = (term34 p x).
Proof. exact (@lem7567651 (term24 p) x). Qed.
Lemma lem7567653 (p : real -> real) (x : real) : (term34 p x) = (term39 p x).
Proof. exact (eq_refl (term34 p x)). Qed.
Lemma lem7567654 (p : real -> real) : (term40 p) = (term24 p).
Proof. exact (fun_ext (fun x : real => @lem7567653 p x)). Qed.
Lemma lem7567655 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7567656 (p : real -> real) (x : real) : (term38 p x) = (term34 p x).
Proof. exact (MK_COMB (@lem7567654 p) (@lem7567655 x)). Qed.
Lemma lem7567657 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7567658 (p : real -> real) (x : real) : (term41 p x) = (term42 p x).
Proof. exact (MK_COMB (@lem7567657) (@lem7567656 p x)). Qed.
Lemma lem7567659 (p : real -> real) (x : real) : (term34 p x) = (term39 p x).
Proof. exact (eq_refl (term34 p x)). Qed.
Lemma lem7567660 (p : real -> real) (x : real) : ((term38 p x) = (term34 p x)) = ((term34 p x) = (term39 p x)).
Proof. exact (MK_COMB (@lem7567658 p x) (@lem7567659 p x)). Qed.
Lemma lem7567661 (p : real -> real) (x : real) : (term34 p x) = (term39 p x).
Proof. exact (EQ_MP (@lem7567660 p x) (@lem7567652 p x)). Qed.
Lemma lem7567662 (p : real -> real) (x : real) : (term35 p x) = (term39 p x).
Proof. exact (TRANS (@lem7567648 p x) (@lem7567661 p x)). Qed.
Lemma lem7567663 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7567664 (p : real -> real) (x : real) : (term32 p x) = (term43 p x).
Proof. exact (MK_COMB (@lem7567663) (@lem7567662 p x)). Qed.
Lemma lem7567666 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem7567595 x) (@lem7567594 x)). Qed.
Lemma lem7567667 (p : real -> real) (x : real) : (term43 p x) = (p x).
Proof. exact (@lem7567666 (p x)). Qed.
Lemma lem7567668 (p : real -> real) (x : real) : (term32 p x) = (p x).
Proof. exact (TRANS (@lem7567664 p x) (@lem7567667 p x)). Qed.
Lemma lem7567669 (p : real -> real) (x : real) : (term31 p x) = (p x).
Proof. exact (TRANS (@lem7567645 p x) (@lem7567668 p x)). Qed.
Lemma lem7567670 (p : real -> real) : (term44 p) = (term45 p).
Proof. exact (fun_ext (fun x : real => @lem7567669 p x)). Qed.
Lemma lem7567671 (t : real -> real) : (term45 t) = t.
Proof. exact (@lem7567599 real real t). Qed.
Lemma lem7567672 (p : real -> real) : (term45 p) = p.
Proof. exact (@lem7567671 p). Qed.
Lemma lem7567673 (p : real -> real) : (term44 p) = p.
Proof. exact (TRANS (@lem7567670 p) (@lem7567672 p)). Qed.
Lemma lem7567674 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7567675 (p : real -> real) : (term28 p) = (polynomial_function p).
Proof. exact (MK_COMB (@lem7567674) (@lem7567673 p)). Qed.
Lemma lem7567676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567677 (p : real -> real) : (term46 p) = (term47 p).
Proof. exact (MK_COMB (@lem7567676) (@lem7567675 p)). Qed.
Lemma lem7567678 (p : real -> real) : (polynomial_function p) = (polynomial_function p).
Proof. exact (eq_refl (polynomial_function p)). Qed.
Lemma lem7567679 (p : real -> real) : (term48 p) = (term49 p).
Proof. exact (MK_COMB (@lem7567677 p) (@lem7567678 p)). Qed.
Lemma lem7567681 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7567682 (p : real -> real) : (term49 p) = True.
Proof. exact (@lem7567681 (polynomial_function p)). Qed.
Lemma lem7567683 (p : real -> real) : (term48 p) = True.
Proof. exact (TRANS (@lem7567679 p) (@lem7567682 p)). Qed.
Lemma lem7567684 (p : real -> real) : True = (term48 p).
Proof. exact (SYM (@lem7567683 p)). Qed.
Lemma lem7567685 (p : real -> real) : term48 p.
Proof. exact (EQ_MP (@lem7567684 p) (@lem0)). Qed.
Lemma lem7567689 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem7567607 x y) (@lem7567606 x y)). Qed.
Lemma lem7567690 (p : real -> real) (x : real) : (term50 p x) = (term51 p x).
Proof. exact (@lem7567689 term33 (p x)). Qed.
Lemma lem7567692 (x : real) : (term5 x) = x.
Proof. exact (EQ_MP (@lem7567601 x) (@lem7567600 x)). Qed.
Lemma lem7567693 (p : real -> real) (x : real) : (term52 p x) = (p x).
Proof. exact (@lem7567692 (p x)). Qed.
Lemma lem7567694 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem7567695 (p : real -> real) (x : real) : (term51 p x) = (term39 p x).
Proof. exact (MK_COMB (@lem7567694) (@lem7567693 p x)). Qed.
Lemma lem7567696 (p : real -> real) (x : real) : (term50 p x) = (term39 p x).
Proof. exact (TRANS (@lem7567690 p x) (@lem7567695 p x)). Qed.
Lemma lem7567697 (p : real -> real) : (term53 p) = (term24 p).
Proof. exact (fun_ext (fun x : real => @lem7567696 p x)). Qed.
Lemma lem7567698 : polynomial_function = polynomial_function.
Proof. exact (eq_refl polynomial_function). Qed.
Lemma lem7567699 (p : real -> real) : (term30 p) = (term22 p).
Proof. exact (MK_COMB (@lem7567698) (@lem7567697 p)). Qed.
Lemma lem7567700 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7567701 (p : real -> real) : (term54 p) = (term55 p).
Proof. exact (MK_COMB (@lem7567700) (@lem7567699 p)). Qed.
Lemma lem7567702 (p : real -> real) : (term22 p) = (term22 p).
Proof. exact (eq_refl (term22 p)). Qed.
Lemma lem7567703 (p : real -> real) : (term56 p) = (term57 p).
Proof. exact (MK_COMB (@lem7567701 p) (@lem7567702 p)). Qed.
Lemma lem7567705 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7567706 (p : real -> real) : (term57 p) = True.
Proof. exact (@lem7567705 (term22 p)). Qed.
Lemma lem7567707 (p : real -> real) : (term56 p) = True.
Proof. exact (TRANS (@lem7567703 p) (@lem7567706 p)). Qed.
Lemma lem7567708 (p : real -> real) : True = (term56 p).
Proof. exact (SYM (@lem7567707 p)). Qed.
Lemma lem7567709 (p : real -> real) : term56 p.
Proof. exact (EQ_MP (@lem7567708 p) (@lem0)). Qed.
Lemma lem7567710 (p : real -> real) (h1 : polynomial_function p) : term22 p.
Proof. exact (@lem7567709 p (@lem7567640 p h1)). Qed.
Lemma lem7567711 (p : real -> real) : term58 p.
Proof. exact (fun h0 : polynomial_function p => @lem7567710 p h0). Qed.
Lemma lem7567712 (p : real -> real) (h1 : term22 p) : polynomial_function p.
Proof. exact (@lem7567685 p (@lem7567633 p h1)). Qed.
Lemma lem7567713 (p : real -> real) : term59 p.
Proof. exact (fun h0 : term22 p => @lem7567712 p h0). Qed.
Lemma lem7567714 (p : real -> real) : term60 p.
Proof. exact (conj (@lem7567713 p) (@lem7567711 p)). Qed.
Lemma lem7567715 (p : real -> real) : (term60 p) = ((term22 p) = (polynomial_function p)).
Proof. exact (@lem32 (term22 p) (polynomial_function p)). Qed.
Lemma lem7567716 (p : real -> real) : (term22 p) = (polynomial_function p).
Proof. exact (EQ_MP (@lem7567715 p) (@lem7567714 p)). Qed.
Lemma lem7567721 : term61.
Proof. exact (fun p : real -> real => @lem7567716 p). Qed.
