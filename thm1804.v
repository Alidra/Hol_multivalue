Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1804_term_abbrevs.
Require Import EQ_REFL_spec.
Require Import IMP_CLAUSES_spec.
Require Import thm7_spec.
Lemma lem1764 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem304 A x). Qed.
Lemma lem1765 {A : Type'} (x : A) : (term0 A x) = (x = x).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem1766 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem1765 A x) (@lem1764 A x)). Qed.
Lemma lem1767 {A : Type'} (x : A) : (x = x) = ((x = x) = True).
Proof. exact (@lem7 (x = x)). Qed.
Lemma lem1769 (t : Prop) : term1 t.
Proof. exact (@lem1763 t). Qed.
Lemma lem1770 (t : Prop) : (term1 t) = (term2 t).
Proof. exact (eq_refl (term1 t)). Qed.
Lemma lem1771 (t : Prop) : term2 t.
Proof. exact (EQ_MP (@lem1770 t) (@lem1769 t)). Qed.
Lemma lem1785 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1767 A x) (@lem1766 A x)). Qed.
Lemma lem1786 {_739 : Type'} (x : _739) : (x = x) = True.
Proof. exact (@lem1785 _739 x). Qed.
Lemma lem1787 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1788 {_739 : Type'} (x : _739) : (term3 _739 x) = (imp True).
Proof. exact (MK_COMB (@lem1787) (@lem1786 _739 x)). Qed.
Lemma lem1789 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem1790 {_739 : Type'} (x : _739) (p : Prop) : (term4 _739 x p) = (True -> p).
Proof. exact (MK_COMB (@lem1788 _739 x) (@lem1789 p)). Qed.
Lemma lem1792 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1771 t)). Qed.
Lemma lem1793 (p : Prop) : (True -> p) = p.
Proof. exact (@lem1792 p). Qed.
Lemma lem1794 {_739 : Type'} (x : _739) (p : Prop) : (term4 _739 x p) = p.
Proof. exact (TRANS (@lem1790 _739 x p) (@lem1793 p)). Qed.
Lemma lem1795 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1796 {_739 : Type'} (x : _739) (p : Prop) : (term5 _739 x p) = (@eq Prop p).
Proof. exact (MK_COMB (@lem1795) (@lem1794 _739 x p)). Qed.
Lemma lem1797 (p : Prop) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem1798 {_739 : Type'} (x : _739) (p : Prop) : ((term4 _739 x p) = p) = (p = p).
Proof. exact (MK_COMB (@lem1796 _739 x p) (@lem1797 p)). Qed.
Lemma lem1800 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1767 A x) (@lem1766 A x)). Qed.
Lemma lem1801 (x : Prop) : (x = x) = True.
Proof. exact (@lem1800 Prop x). Qed.
Lemma lem1802 (p : Prop) : (p = p) = True.
Proof. exact (@lem1801 p). Qed.
Lemma lem1803 {_739 : Type'} (x : _739) (p : Prop) : ((term4 _739 x p) = p) = True.
Proof. exact (TRANS (@lem1798 _739 x p) (@lem1802 p)). Qed.
Lemma lem1804 {_739 : Type'} (x : _739) (p : Prop) : True = ((term4 _739 x p) = p).
Proof. exact (SYM (@lem1803 _739 x p)). Qed.
