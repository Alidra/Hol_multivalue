Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_NEG_term_abbrevs.
Require Import REAL_ABS_NEG_spec.
Require Import REAL_POW_NEG_spec.
Require Import REAL_SGN_NEG_spec.
Require Import SQRT_UNIQUE_GEN_spec.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm516372_spec.
Lemma lem1921052 (x : real) : term0 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1921053 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1921054 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1921053 x) (@lem1921052 x)). Qed.
Lemma lem1921467 : term2.
Proof. exact (EQ_MP (@lem516372) (@lem0)). Qed.
Lemma lem1921468 : term3.
Proof. exact (proj2 (@lem1921467)). Qed.
Lemma lem1921469 : term4.
Proof. exact (proj2 (@lem1921468)). Qed.
Lemma lem1921474 : term5.
Proof. exact (proj1 (@lem1921469)). Qed.
Lemma lem1921475 (n : nat) : term6 n.
Proof. exact (@lem1921474 n). Qed.
Lemma lem1921476 (n : nat) : (term6 n) = ((term7 n) = True).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem1921479 : term8.
Proof. exact (proj1 (@lem1921467)). Qed.
Lemma lem1921480 (n : nat) : term9 n.
Proof. exact (@lem1921479 n). Qed.
Lemma lem1921481 (n : nat) : (term9 n) = ((term10 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem1921701 (x : real) : term11 x.
Proof. exact (@lem1365032 x). Qed.
Lemma lem1921702 (x : real) : (term11 x) = ((term12 x) = (real_abs x)).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1921704 (x : real) : term13 x.
Proof. exact (@lem1362863 x). Qed.
Lemma lem1921705 (x : real) : (term13 x) = (term14 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1921706 (x : real) : term14 x.
Proof. exact (EQ_MP (@lem1921705 x) (@lem1921704 x)). Qed.
Lemma lem1921707 (x : real) (n : nat) : term15 x n.
Proof. exact (@lem1921706 x n). Qed.
Lemma lem1921708 (x : real) (n : nat) : (term15 x n) = ((term16 x n) = (term17 x n)).
Proof. exact (eq_refl (term15 x n)). Qed.
Lemma lem1921710 (x : real) : term18 x.
Proof. exact (@lem1715400 x). Qed.
Lemma lem1921711 (x : real) : (term18 x) = ((term19 x) = (term20 x)).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1921713 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1921714 (x : real) (h1 : term21) : term22 x.
Proof. exact (@lem1921713 h1 x). Qed.
Lemma lem1921715 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1921716 (x : real) (h1 : term21) : term23 x.
Proof. exact (EQ_MP (@lem1921715 x) (@lem1921714 x h1)). Qed.
Lemma lem1921717 (x : real) (y : real) (h1 : term21) : term24 x y.
Proof. exact (@lem1921716 x h1 y). Qed.
Lemma lem1921718 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1921719 (x : real) (y : real) (h1 : term21) : term25 x y.
Proof. exact (EQ_MP (@lem1921718 x y) (@lem1921717 x y h1)). Qed.
Lemma lem1921720 (y : real) (x : real) (h1 : term26 y x) : term26 y x.
Proof. exact (h1). Qed.
Lemma lem1921721 (y : real) (x : real) (h1 : term21) (h2 : term26 y x) : (sqrt x) = y.
Proof. exact (@lem1921719 x y h1 (@lem1921720 y x h2)). Qed.
Lemma lem1921722 (y : real) (x : real) (h1 : term26 y x) : term27 x y.
Proof. exact (fun h0 : term21 => @lem1921721 y x h0 h1). Qed.
Lemma lem1921723 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem1921724 (y : real) (x : real) (h1 : term21) (h2 : term26 y x) : (sqrt x) = y.
Proof. exact (@lem1921722 y x h2 (@lem1921723 h1)). Qed.
Lemma lem1921725 (x : real) (y : real) (h1 : term21) : term25 x y.
Proof. exact (fun h0 : term26 y x => @lem1921724 y x h1 h0). Qed.
Lemma lem1921726 (x : real) (h1 : term21) : term23 x.
Proof. exact (fun y : real => @lem1921725 x y h1). Qed.
Lemma lem1921727 (h1 : term21) : term21.
Proof. exact (fun x : real => @lem1921726 x h1). Qed.
Lemma lem1921728 : term28.
Proof. exact (fun h0 : term21 => @lem1921727 h0). Qed.
Lemma lem1921729 : term21.
Proof. exact (@lem1921728 (@lem1921051)). Qed.
Lemma lem1921730 (x : real) : term22 x.
Proof. exact (@lem1921729 x). Qed.
Lemma lem1921731 (x : real) : (term22 x) = (term23 x).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1921732 (x : real) : term23 x.
Proof. exact (EQ_MP (@lem1921731 x) (@lem1921730 x)). Qed.
Lemma lem1921733 (x : real) (y : real) : term24 x y.
Proof. exact (@lem1921732 x y). Qed.
Lemma lem1921734 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1921737 (x : real) (y : real) : term25 x y.
Proof. exact (EQ_MP (@lem1921734 x y) (@lem1921733 x y)). Qed.
Lemma lem1921738 (x : real) : term29 x.
Proof. exact (@lem1921737 (real_neg x) (term30 x)). Qed.
Lemma lem1921744 (x : real) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1921711 x) (@lem1921710 x)). Qed.
Lemma lem1921745 (x : real) : (term31 x) = (term32 x).
Proof. exact (@lem1921744 (sqrt x)). Qed.
Lemma lem1921746 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1921747 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1921746) (@lem1921745 x)). Qed.
Lemma lem1921749 (x : real) : (term19 x) = (term20 x).
Proof. exact (EQ_MP (@lem1921711 x) (@lem1921710 x)). Qed.
Lemma lem1921750 (x : real) : ((term31 x) = (term19 x)) = ((term32 x) = (term20 x)).
Proof. exact (MK_COMB (@lem1921747 x) (@lem1921749 x)). Qed.
Lemma lem1921753 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1921754 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1921753) (@lem1921750 x)). Qed.
Lemma lem1921758 (x : real) (n : nat) : (term16 x n) = (term17 x n).
Proof. exact (EQ_MP (@lem1921708 x n) (@lem1921707 x n)). Qed.
Lemma lem1921759 (x : real) : (term37 x) = (term38 x).
Proof. exact (@lem1921758 (sqrt x) term39). Qed.
Lemma lem1921761 (n : nat) : (term10 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1921481 n) (@lem1921480 n)). Qed.
Lemma lem1921762 : term40 = term41.
Proof. exact (@lem1921761 term42). Qed.
Lemma lem1921764 (n : nat) : (term7 n) = True.
Proof. exact (EQ_MP (@lem1921476 n) (@lem1921475 n)). Qed.
Lemma lem1921765 : term41 = True.
Proof. exact (@lem1921764 (BIT1 0)). Qed.
Lemma lem1921766 : term40 = True.
Proof. exact (TRANS (@lem1921762) (@lem1921765)). Qed.
Lemma lem1921767 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1921768 : term43 = (@COND real True).
Proof. exact (MK_COMB (@lem1921767) (@lem1921766)). Qed.
Lemma lem1921769 (x : real) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1921770 (x : real) : (term45 x) = (term46 x).
Proof. exact (MK_COMB (@lem1921768) (@lem1921769 x)). Qed.
Lemma lem1921771 (x : real) : (term47 x) = (term47 x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1921772 (x : real) : (term38 x) = (term48 x).
Proof. exact (MK_COMB (@lem1921770 x) (@lem1921771 x)). Qed.
Lemma lem1921774 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1921775 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1921774 real t2 t1). Qed.
Lemma lem1921776 (x : real) : (term48 x) = (term44 x).
Proof. exact (@lem1921775 (term47 x) (term44 x)). Qed.
Lemma lem1921777 (x : real) : (term38 x) = (term44 x).
Proof. exact (TRANS (@lem1921772 x) (@lem1921776 x)). Qed.
Lemma lem1921778 (x : real) : (term37 x) = (term44 x).
Proof. exact (TRANS (@lem1921759 x) (@lem1921777 x)). Qed.
Lemma lem1921779 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1921780 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1921779) (@lem1921778 x)). Qed.
Lemma lem1921782 (x : real) : (term12 x) = (real_abs x).
Proof. exact (EQ_MP (@lem1921702 x) (@lem1921701 x)). Qed.
Lemma lem1921783 (x : real) : ((term37 x) = (term12 x)) = ((term44 x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1921780 x) (@lem1921782 x)). Qed.
Lemma lem1921786 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1921754 x) (@lem1921783 x)). Qed.
Lemma lem1921789 (x : real) : (term52 x) = (term51 x).
Proof. exact (SYM (@lem1921786 x)). Qed.
Lemma lem1921795 (x : real) : (term53 x) = (real_sgn x).
Proof. exact (proj1 (@lem1921054 x)). Qed.
Lemma lem1921796 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1921797 (x : real) : (term32 x) = (term20 x).
Proof. exact (MK_COMB (@lem1921796) (@lem1921795 x)). Qed.
Lemma lem1921798 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1921799 (x : real) : (term34 x) = (term54 x).
Proof. exact (MK_COMB (@lem1921798) (@lem1921797 x)). Qed.
Lemma lem1921800 (x : real) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1921801 (x : real) : ((term32 x) = (term20 x)) = ((term20 x) = (term20 x)).
Proof. exact (MK_COMB (@lem1921799 x) (@lem1921800 x)). Qed.
Lemma lem1921803 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1921804 (x : real) : (x = x) = True.
Proof. exact (@lem1921803 real x). Qed.
Lemma lem1921805 (x : real) : ((term20 x) = (term20 x)) = True.
Proof. exact (@lem1921804 (term20 x)). Qed.
Lemma lem1921806 (x : real) : ((term32 x) = (term20 x)) = True.
Proof. exact (TRANS (@lem1921801 x) (@lem1921805 x)). Qed.
Lemma lem1921807 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1921808 (x : real) : (term36 x) = (and True).
Proof. exact (MK_COMB (@lem1921807) (@lem1921806 x)). Qed.
Lemma lem1921812 (x : real) : (term44 x) = (real_abs x).
Proof. exact (proj2 (@lem1921054 x)). Qed.
Lemma lem1921813 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1921814 (x : real) : (term50 x) = (term55 x).
Proof. exact (MK_COMB (@lem1921813) (@lem1921812 x)). Qed.
Lemma lem1921815 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1921816 (x : real) : ((term44 x) = (real_abs x)) = ((real_abs x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1921814 x) (@lem1921815 x)). Qed.
Lemma lem1921818 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1921819 (x : real) : (x = x) = True.
Proof. exact (@lem1921818 real x). Qed.
Lemma lem1921820 (x : real) : ((real_abs x) = (real_abs x)) = True.
Proof. exact (@lem1921819 (real_abs x)). Qed.
Lemma lem1921821 (x : real) : ((term44 x) = (real_abs x)) = True.
Proof. exact (TRANS (@lem1921816 x) (@lem1921820 x)). Qed.
Lemma lem1921822 (x : real) : (term52 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1921808 x) (@lem1921821 x)). Qed.
Lemma lem1921824 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1921825 : (True /\ True) = True.
Proof. exact (@lem1921824 True). Qed.
Lemma lem1921826 (x : real) : (term52 x) = True.
Proof. exact (TRANS (@lem1921822 x) (@lem1921825)). Qed.
Lemma lem1921827 (x : real) : True = (term52 x).
Proof. exact (SYM (@lem1921826 x)). Qed.
Lemma lem1921828 (x : real) : term52 x.
Proof. exact (EQ_MP (@lem1921827 x) (@lem0)). Qed.
Lemma lem1921829 (x : real) : term51 x.
Proof. exact (EQ_MP (@lem1921789 x) (@lem1921828 x)). Qed.
Lemma lem1921830 (x : real) : (term56 x) = (term30 x).
Proof. exact (@lem1921738 x (@lem1921829 x)). Qed.
Lemma lem1921835 : term57.
Proof. exact (fun x : real => @lem1921830 x). Qed.
