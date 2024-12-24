Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3457131_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18394_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3453857_spec.
Lemma lem3455585 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3455586 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term1 _89578 _89597 _89598 P f) = (term2 _89578 _89597 _89598 P f).
Proof. exact (@lem3455585 (term1 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455587 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term2 _89578 _89597 _89598 P f) = (term1 _89578 _89597 _89598 P f).
Proof. exact (SYM (@lem3455586 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455588 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term3 _89578 _89597 _89598 P f) : term3 _89578 _89597 _89598 P f.
Proof. exact (h1). Qed.
Lemma lem3455591 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term2 _89578 _89597 _89598 P f) : term2 _89578 _89597 _89598 P f.
Proof. exact (h1). Qed.
Lemma lem3455592 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term4 _89578 _89597 _89598 P f.
Proof. exact (fun h0 : term2 _89578 _89597 _89598 P f => @lem3455591 _89578 _89597 _89598 P f h0). Qed.
Lemma lem3455593 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term4 _89578 _89597 _89598 P f) : term4 _89578 _89597 _89598 P f.
Proof. exact (h1). Qed.
Lemma lem3455594 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term2 _89578 _89597 _89598 P f) : term2 _89578 _89597 _89598 P f.
Proof. exact (h1). Qed.
Lemma lem3455595 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term2 _89578 _89597 _89598 P f) (h2 : term4 _89578 _89597 _89598 P f) : term2 _89578 _89597 _89598 P f.
Proof. exact (@lem3455593 _89578 _89597 _89598 P f h2 (@lem3455594 _89578 _89597 _89598 P f h1)). Qed.
Lemma lem3455596 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term2 _89578 _89597 _89598 P f) : term5 _89578 _89597 _89598 P f.
Proof. exact (fun h0 : term4 _89578 _89597 _89598 P f => @lem3455595 _89578 _89597 _89598 P f h1 h0). Qed.
Lemma lem3455597 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term4 _89578 _89597 _89598 P f) : term4 _89578 _89597 _89598 P f.
Proof. exact (h1). Qed.
Lemma lem3455598 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term2 _89578 _89597 _89598 P f) (h2 : term4 _89578 _89597 _89598 P f) : term2 _89578 _89597 _89598 P f.
Proof. exact (@lem3455596 _89578 _89597 _89598 P f h1 (@lem3455597 _89578 _89597 _89598 P f h2)). Qed.
Lemma lem3455599 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term4 _89578 _89597 _89598 P f) : term4 _89578 _89597 _89598 P f.
Proof. exact (fun h0 : term2 _89578 _89597 _89598 P f => @lem3455598 _89578 _89597 _89598 P f h0 h1). Qed.
Lemma lem3455600 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term6 _89578 _89597 _89598 P f.
Proof. exact (fun h0 : term4 _89578 _89597 _89598 P f => @lem3455599 _89578 _89597 _89598 P f h0). Qed.
Lemma lem3455603 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term4 _89578 _89597 _89598 P f.
Proof. exact (@lem3455600 _89578 _89597 _89598 P f (@lem3455592 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455604 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term4 _89578 _89597 _89598 P f.
Proof. exact (@lem3455603 _89578 _89597 _89598 P f). Qed.
Lemma lem3455614 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3455615 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term2 _89578 _89597 _89598 P f) = (term7 _89578 _89597 _89598 P f).
Proof. exact (@lem3455614 (term3 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455617 (t : Prop) : (term8 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3455618 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term7 _89578 _89597 _89598 P f) = (term1 _89578 _89597 _89598 P f).
Proof. exact (@lem3455617 (term1 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455623 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term2 _89578 _89597 _89598 P f) = (term1 _89578 _89597 _89598 P f).
Proof. exact (TRANS (@lem3455615 _89578 _89597 _89598 P f) (@lem3455618 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455782 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : (term9 _89578 _89597 _89598 f) = (term10 _89578 _89597 _89598 f).
Proof. exact (fun_ext (fun P : type1470 _89597 _89598 => @lem3455623 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455783 {_89597 _89598 : Type'} : (@all (_89598 -> _89597 -> Prop)) = (@all (_89598 -> _89597 -> Prop)).
Proof. exact (eq_refl (@all (_89598 -> _89597 -> Prop))). Qed.
Lemma lem3455784 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : (term11 _89578 _89597 _89598 f) = (term12 _89578 _89597 _89598 f).
Proof. exact (MK_COMB (@lem3455783 _89597 _89598) (@lem3455782 _89578 _89597 _89598 f)). Qed.
Lemma lem3455789 {_89578 _89597 _89598 : Type'} : (term13 _89578 _89597 _89598) = (term14 _89578 _89597 _89598).
Proof. exact (fun_ext (fun f : type1517 _89578 _89597 _89598 => @lem3455784 _89578 _89597 _89598 f)). Qed.
Lemma lem3455790 {_89578 _89597 _89598 : Type'} : (@all (_89598 -> _89597 -> _89578 -> Prop)) = (@all (_89598 -> _89597 -> _89578 -> Prop)).
Proof. exact (eq_refl (@all (_89598 -> _89597 -> _89578 -> Prop))). Qed.
Lemma lem3455799 {_89578 _89597 _89598 : Type'} : (term15 _89578 _89597 _89598) = (term16 _89578 _89597 _89598).
Proof. exact (MK_COMB (@lem3455790 _89578 _89597 _89598) (@lem3455789 _89578 _89597 _89598)). Qed.
Lemma lem3455804 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term17 _89578 _89597 _89598 P x f x' y) = (term17 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term17 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455805 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term18 _89578 _89597 _89598 P x f x') = (term18 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3455804 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455806 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3455807 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term19 _89578 _89597 _89598 P x f x') = (term19 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3455806 _89597) (@lem3455805 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455808 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term20 _89578 _89597 _89598 P x f) = (term20 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3455807 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455809 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3455810 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term21 _89578 _89597 _89598 P x f) = (term21 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3455809 _89598) (@lem3455808 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3455811 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3455816 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term22 _89578 _89597 _89598 P t f x y) = (term22 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term22 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455817 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term23 _89578 _89597 _89598 P t f x) = (term23 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3455816 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455818 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3455819 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term24 _89578 _89597 _89598 P t f x) = (term24 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3455818 _89597) (@lem3455817 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455820 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term25 _89578 _89597 _89598 P t f) = (term25 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3455819 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455821 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3455822 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term26 _89578 _89597 _89598 P t f) = (term26 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3455821 _89598) (@lem3455820 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455824 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term27 _89578 _89597 _89598 P t f) = (term27 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3455823) (@lem3455822 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455825 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term28 _89578 _89597 _89598 P f x t) = (term28 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3455824 _89578 _89597 _89598 P t f) (@lem3455811 _89578 x t)). Qed.
Lemma lem3455826 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term29 _89578 _89597 _89598 P f x) = (term29 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3455825 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455827 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3455828 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term30 _89578 _89597 _89598 P f x) = (term30 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3455827 _89578) (@lem3455826 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3455829 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3455830 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term31 _89578 _89597 _89598 P f x) = (term31 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3455829) (@lem3455828 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3455831 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term30 _89578 _89597 _89598 P f x) = (term21 _89578 _89597 _89598 P x f)) = ((term30 _89578 _89597 _89598 P f x) = (term21 _89578 _89597 _89598 P x f)).
Proof. exact (MK_COMB (@lem3455830 _89578 _89597 _89598 P f x) (@lem3455810 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3455832 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term32 _89578 _89597 _89598 P f) = (term32 _89578 _89597 _89598 P f).
Proof. exact (fun_ext (fun x : _89578 => @lem3455831 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3455833 {_89578 : Type'} : (@all _89578) = (@all _89578).
Proof. exact (eq_refl (@all _89578)). Qed.
Lemma lem3455834 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term1 _89578 _89597 _89598 P f) = (term1 _89578 _89597 _89598 P f).
Proof. exact (MK_COMB (@lem3455833 _89578) (@lem3455832 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455835 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : (term10 _89578 _89597 _89598 f) = (term10 _89578 _89597 _89598 f).
Proof. exact (fun_ext (fun P : type1470 _89597 _89598 => @lem3455834 _89578 _89597 _89598 P f)). Qed.
Lemma lem3455836 {_89597 _89598 : Type'} : (@all (_89598 -> _89597 -> Prop)) = (@all (_89598 -> _89597 -> Prop)).
Proof. exact (eq_refl (@all (_89598 -> _89597 -> Prop))). Qed.
Lemma lem3455837 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : (term12 _89578 _89597 _89598 f) = (term12 _89578 _89597 _89598 f).
Proof. exact (MK_COMB (@lem3455836 _89597 _89598) (@lem3455835 _89578 _89597 _89598 f)). Qed.
Lemma lem3455838 {_89578 _89597 _89598 : Type'} : (term14 _89578 _89597 _89598) = (term14 _89578 _89597 _89598).
Proof. exact (fun_ext (fun f : type1517 _89578 _89597 _89598 => @lem3455837 _89578 _89597 _89598 f)). Qed.
Lemma lem3455839 {_89578 _89597 _89598 : Type'} : (@all (_89598 -> _89597 -> _89578 -> Prop)) = (@all (_89598 -> _89597 -> _89578 -> Prop)).
Proof. exact (eq_refl (@all (_89598 -> _89597 -> _89578 -> Prop))). Qed.
Lemma lem3455840 {_89578 _89597 _89598 : Type'} : (term16 _89578 _89597 _89598) = (term16 _89578 _89597 _89598).
Proof. exact (MK_COMB (@lem3455839 _89578 _89597 _89598) (@lem3455838 _89578 _89597 _89598)). Qed.
Lemma lem3455897 {_89578 _89597 _89598 : Type'} : (term15 _89578 _89597 _89598) = (term16 _89578 _89597 _89598).
Proof. exact (TRANS (@lem3455799 _89578 _89597 _89598) (@lem3455840 _89578 _89597 _89598)). Qed.
Lemma lem3455898 {_89578 _89597 _89598 : Type'} : (term16 _89578 _89597 _89598) = (term15 _89578 _89597 _89598).
Proof. exact (SYM (@lem3455897 _89578 _89597 _89598)). Qed.
Lemma lem3455900 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3455901 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term30 _89578 _89597 _89598 P f x) = (term21 _89578 _89597 _89598 P x f)) = (term33 _89578 _89597 _89598 P x f).
Proof. exact (@lem3455900 ((term30 _89578 _89597 _89598 P f x) = (term21 _89578 _89597 _89598 P x f))). Qed.
Lemma lem3455902 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term33 _89578 _89597 _89598 P x f) = ((term30 _89578 _89597 _89598 P f x) = (term21 _89578 _89597 _89598 P x f)).
Proof. exact (SYM (@lem3455901 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3455903 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term34 _89578 _89597 _89598 P x f) : term34 _89578 _89597 _89598 P x f.
Proof. exact (h1). Qed.
Lemma lem3455912 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term35 _89578 _89597 _89598 P t f x y) = (term36 _89578 _89597 _89598 P t f x y).
Proof. exact (@lem17045 (P x y) (t = (f x y))). Qed.
Lemma lem3455915 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term22 _89578 _89597 _89598 P t f x y) = (term22 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term22 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455916 {_89597 : Type'} (P : _89597 -> Prop) : (term37 _89597 P) = (term38 _89597 P).
Proof. exact (@lem18394 _89597 P). Qed.
Lemma lem3455917 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term39 _89578 _89597 _89598 P t f x) = (term40 _89578 _89597 _89598 P t f x).
Proof. exact (@lem3455916 _89597 (term23 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455918 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term41 _89578 _89597 _89598 P t f x y) = (term22 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term41 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455919 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3455920 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term42 _89578 _89597 _89598 P t f x y) = (term35 _89578 _89597 _89598 P t f x y).
Proof. exact (MK_COMB (@lem3455919) (@lem3455918 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455921 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term42 _89578 _89597 _89598 P t f x y) = (term36 _89578 _89597 _89598 P t f x y).
Proof. exact (TRANS (@lem3455920 _89578 _89597 _89598 P t f x y) (@lem3455912 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455922 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term43 _89578 _89597 _89598 P t f x) = (term44 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3455921 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455923 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3455924 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term40 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3455923 _89597) (@lem3455922 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455925 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term39 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (TRANS (@lem3455917 _89578 _89597 _89598 P t f x) (@lem3455924 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455926 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term23 _89578 _89597 _89598 P t f x) = (term23 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3455915 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3455927 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3455928 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term24 _89578 _89597 _89598 P t f x) = (term24 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3455927 _89597) (@lem3455926 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455929 {_89598 : Type'} (P : _89598 -> Prop) : (term37 _89598 P) = (term38 _89598 P).
Proof. exact (@lem18394 _89598 P). Qed.
Lemma lem3455930 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term46 _89578 _89597 _89598 P t f) = (term47 _89578 _89597 _89598 P t f).
Proof. exact (@lem3455929 _89598 (term25 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455931 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term48 _89578 _89597 _89598 P t f x) = (term24 _89578 _89597 _89598 P t f x).
Proof. exact (eq_refl (term48 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3455933 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term49 _89578 _89597 _89598 P t f x) = (term39 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3455932) (@lem3455931 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455934 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term49 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (TRANS (@lem3455933 _89578 _89597 _89598 P t f x) (@lem3455925 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455935 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term50 _89578 _89597 _89598 P t f) = (term51 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3455934 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455936 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3455937 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term47 _89578 _89597 _89598 P t f) = (term52 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3455936 _89598) (@lem3455935 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455938 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term46 _89578 _89597 _89598 P t f) = (term52 _89578 _89597 _89598 P t f).
Proof. exact (TRANS (@lem3455930 _89578 _89597 _89598 P t f) (@lem3455937 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455939 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term25 _89578 _89597 _89598 P t f) = (term25 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3455928 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3455940 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3455941 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term26 _89578 _89597 _89598 P t f) = (term26 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3455940 _89598) (@lem3455939 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455942 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term53 _89578 x t) = (term53 _89578 x t).
Proof. exact (eq_refl (term53 _89578 x t)). Qed.
Lemma lem3455943 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3455944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3455945 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term54 _89578 _89597 _89598 P t f) = (term55 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3455944) (@lem3455938 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455946 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term56 _89578 _89597 _89598 P f x t) = (term57 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3455945 _89578 _89597 _89598 P t f) (@lem3455942 _89578 x t)). Qed.
Lemma lem3455947 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term58 _89578 _89597 _89598 P f x t) = (term56 _89578 _89597 _89598 P f x t).
Proof. exact (@lem17045 (term26 _89578 _89597 _89598 P t f) (@IN _89578 x t)). Qed.
Lemma lem3455948 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term58 _89578 _89597 _89598 P f x t) = (term57 _89578 _89597 _89598 P f x t).
Proof. exact (TRANS (@lem3455947 _89578 _89597 _89598 P f x t) (@lem3455946 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455949 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3455950 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term27 _89578 _89597 _89598 P t f) = (term27 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3455949) (@lem3455941 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3455951 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term28 _89578 _89597 _89598 P f x t) = (term28 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3455950 _89578 _89597 _89598 P t f) (@lem3455943 _89578 x t)). Qed.
Lemma lem3455952 {_89578 : Type'} (P : type686 _89578) : (term59 _89578 P) = (term60 _89578 P).
Proof. exact (@lem18394 (_89578 -> Prop) P). Qed.
Lemma lem3455953 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term61 _89578 _89597 _89598 P f x) = (term62 _89578 _89597 _89598 P f x).
Proof. exact (@lem3455952 _89578 (term29 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3455954 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term63 _89578 _89597 _89598 P f x t) = (term28 _89578 _89597 _89598 P f x t).
Proof. exact (eq_refl (term63 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455955 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3455956 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term64 _89578 _89597 _89598 P f x t) = (term58 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3455955) (@lem3455954 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455957 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term64 _89578 _89597 _89598 P f x t) = (term57 _89578 _89597 _89598 P f x t).
Proof. exact (TRANS (@lem3455956 _89578 _89597 _89598 P f x t) (@lem3455948 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455958 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term65 _89578 _89597 _89598 P f x) = (term66 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3455957 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455959 {_89578 : Type'} : (@all (_89578 -> Prop)) = (@all (_89578 -> Prop)).
Proof. exact (eq_refl (@all (_89578 -> Prop))). Qed.
Lemma lem3455960 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term62 _89578 _89597 _89598 P f x) = (term67 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3455959 _89578) (@lem3455958 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3455961 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term61 _89578 _89597 _89598 P f x) = (term67 _89578 _89597 _89598 P f x).
Proof. exact (TRANS (@lem3455953 _89578 _89597 _89598 P f x) (@lem3455960 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3455962 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term29 _89578 _89597 _89598 P f x) = (term29 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3455951 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3455963 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3455964 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term30 _89578 _89597 _89598 P f x) = (term30 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3455963 _89578) (@lem3455962 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3455973 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term68 _89578 _89597 _89598 P x f x' y) = (term69 _89578 _89597 _89598 P x f x' y).
Proof. exact (@lem17045 (P x' y) (term70 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3455976 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term17 _89578 _89597 _89598 P x f x' y) = (term17 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term17 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455977 {_89597 : Type'} (P : _89597 -> Prop) : (term37 _89597 P) = (term38 _89597 P).
Proof. exact (@lem18394 _89597 P). Qed.
Lemma lem3455978 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term71 _89578 _89597 _89598 P x f x') = (term72 _89578 _89597 _89598 P x f x').
Proof. exact (@lem3455977 _89597 (term18 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455979 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term73 _89578 _89597 _89598 P x f x' y) = (term17 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term73 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455980 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3455981 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term74 _89578 _89597 _89598 P x f x' y) = (term68 _89578 _89597 _89598 P x f x' y).
Proof. exact (MK_COMB (@lem3455980) (@lem3455979 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455982 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term74 _89578 _89597 _89598 P x f x' y) = (term69 _89578 _89597 _89598 P x f x' y).
Proof. exact (TRANS (@lem3455981 _89578 _89597 _89598 P x f x' y) (@lem3455973 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455983 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term75 _89578 _89597 _89598 P x f x') = (term76 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3455982 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455984 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3455985 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term72 _89578 _89597 _89598 P x f x') = (term77 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3455984 _89597) (@lem3455983 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455986 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term71 _89578 _89597 _89598 P x f x') = (term77 _89578 _89597 _89598 P x f x').
Proof. exact (TRANS (@lem3455978 _89578 _89597 _89598 P x f x') (@lem3455985 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455987 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term18 _89578 _89597 _89598 P x f x') = (term18 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3455976 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3455988 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3455989 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term19 _89578 _89597 _89598 P x f x') = (term19 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3455988 _89597) (@lem3455987 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455990 {_89598 : Type'} (P : _89598 -> Prop) : (term37 _89598 P) = (term38 _89598 P).
Proof. exact (@lem18394 _89598 P). Qed.
Lemma lem3455991 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term78 _89578 _89597 _89598 P x f) = (term79 _89578 _89597 _89598 P x f).
Proof. exact (@lem3455990 _89598 (term20 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3455992 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term80 _89578 _89597 _89598 P x f x') = (term19 _89578 _89597 _89598 P x f x').
Proof. exact (eq_refl (term80 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455993 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3455994 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term81 _89578 _89597 _89598 P x f x') = (term71 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3455993) (@lem3455992 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455995 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term81 _89578 _89597 _89598 P x f x') = (term77 _89578 _89597 _89598 P x f x').
Proof. exact (TRANS (@lem3455994 _89578 _89597 _89598 P x f x') (@lem3455986 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455996 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term82 _89578 _89597 _89598 P x f) = (term83 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3455995 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3455997 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3455998 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term79 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3455997 _89598) (@lem3455996 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3455999 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term78 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3455991 _89578 _89597 _89598 P x f) (@lem3455998 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456000 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term20 _89578 _89597 _89598 P x f) = (term20 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3455989 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456001 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456002 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term21 _89578 _89597 _89598 P x f) = (term21 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456001 _89598) (@lem3456000 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456003 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456004 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term85 _89578 _89597 _89598 P f x) = (term86 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456003) (@lem3455961 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456005 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term87 _89578 _89597 _89598 P x f) = (term88 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456004 _89578 _89597 _89598 P f x) (@lem3456002 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456007 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term89 _89578 _89597 _89598 P f x) = (term89 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456006) (@lem3455964 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456008 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term90 _89578 _89597 _89598 P x f) = (term91 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456007 _89578 _89597 _89598 P f x) (@lem3455999 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456009 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456010 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term92 _89578 _89597 _89598 P x f) = (term93 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456009) (@lem3456008 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456011 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term94 _89578 _89597 _89598 P x f) = (term95 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456010 _89578 _89597 _89598 P x f) (@lem3456005 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456012 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term34 _89578 _89597 _89598 P x f) = (term94 _89578 _89597 _89598 P x f).
Proof. exact (@lem17646 (term30 _89578 _89597 _89598 P f x) (term21 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456013 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term34 _89578 _89597 _89598 P x f) = (term95 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456012 _89578 _89597 _89598 P x f) (@lem3456011 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456320 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3456321 {_89598 : Type'} (P : _89598 -> Prop) (Q : Prop) : (term96 _89598 P Q) = (term97 _89598 P Q).
Proof. exact (@lem3456320 _89598 P Q). Qed.
Lemma lem3456322 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term98 _89578 _89597 _89598 P f x t) = (term99 _89578 _89597 _89598 P f x t).
Proof. exact (@lem3456321 _89598 (term25 _89578 _89597 _89598 P t f) (@IN _89578 x t)). Qed.
Lemma lem3456323 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term48 _89578 _89597 _89598 P t f x) = (term24 _89578 _89597 _89598 P t f x).
Proof. exact (eq_refl (term48 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456324 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term100 _89578 _89597 _89598 P t f) = (term25 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3456323 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456325 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456326 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term101 _89578 _89597 _89598 P t f) = (term26 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3456325 _89598) (@lem3456324 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3456327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456328 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term102 _89578 _89597 _89598 P t f) = (term27 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3456327) (@lem3456326 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3456329 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3456330 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term98 _89578 _89597 _89598 P f x t) = (term28 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456328 _89578 _89597 _89598 P t f) (@lem3456329 _89578 x t)). Qed.
Lemma lem3456331 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456332 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term103 _89578 _89597 _89598 P f x t) = (term104 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456331) (@lem3456330 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456333 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term48 _89578 _89597 _89598 P t f x) = (term24 _89578 _89597 _89598 P t f x).
Proof. exact (eq_refl (term48 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456334 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456335 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term105 _89578 _89597 _89598 P t f x) = (term106 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456334) (@lem3456333 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456336 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3456337 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term107 _89578 _89597 _89598 P f x x' t) = (term108 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456335 _89578 _89597 _89598 P t f x) (@lem3456336 _89578 x' t)). Qed.
Lemma lem3456338 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term109 _89578 _89597 _89598 P f x t) = (term110 _89578 _89597 _89598 P f x t).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456337 _89578 _89597 _89598 P f x' x t)). Qed.
Lemma lem3456339 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456340 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term99 _89578 _89597 _89598 P f x t) = (term111 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456339 _89598) (@lem3456338 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456341 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : ((term98 _89578 _89597 _89598 P f x t) = (term99 _89578 _89597 _89598 P f x t)) = ((term28 _89578 _89597 _89598 P f x t) = (term111 _89578 _89597 _89598 P f x t)).
Proof. exact (MK_COMB (@lem3456332 _89578 _89597 _89598 P f x t) (@lem3456340 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456342 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term28 _89578 _89597 _89598 P f x t) = (term111 _89578 _89597 _89598 P f x t).
Proof. exact (EQ_MP (@lem3456341 _89578 _89597 _89598 P f x t) (@lem3456322 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456344 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3456345 {_89597 : Type'} (P : _89597 -> Prop) (Q : Prop) : (term96 _89597 P Q) = (term97 _89597 P Q).
Proof. exact (@lem3456344 _89597 P Q). Qed.
Lemma lem3456346 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term112 _89578 _89597 _89598 P f x x' t) = (term113 _89578 _89597 _89598 P f x x' t).
Proof. exact (@lem3456345 _89597 (term23 _89578 _89597 _89598 P t f x) (@IN _89578 x' t)). Qed.
Lemma lem3456347 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term41 _89578 _89597 _89598 P t f x y) = (term22 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term41 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456348 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term114 _89578 _89597 _89598 P t f x) = (term23 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3456347 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456349 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456350 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term115 _89578 _89597 _89598 P t f x) = (term24 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456349 _89597) (@lem3456348 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456352 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term116 _89578 _89597 _89598 P t f x) = (term106 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456351) (@lem3456350 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456353 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3456354 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term112 _89578 _89597 _89598 P f x x' t) = (term108 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456352 _89578 _89597 _89598 P t f x) (@lem3456353 _89578 x' t)). Qed.
Lemma lem3456355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456356 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term117 _89578 _89597 _89598 P f x x' t) = (term118 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456355) (@lem3456354 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456357 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term41 _89578 _89597 _89598 P t f x y) = (term22 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term41 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456359 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term119 _89578 _89597 _89598 P t f x y) = (term120 _89578 _89597 _89598 P t f x y).
Proof. exact (MK_COMB (@lem3456358) (@lem3456357 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456360 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (@IN _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (@IN _89578 x t)). Qed.
Lemma lem3456361 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) (x' : _89578) (t : _89578 -> Prop) : (term121 _89578 _89597 _89598 P f x y x' t) = (term122 _89578 _89597 _89598 P f x y x' t).
Proof. exact (MK_COMB (@lem3456359 _89578 _89597 _89598 P t f x y) (@lem3456360 _89578 x' t)). Qed.
Lemma lem3456362 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term123 _89578 _89597 _89598 P f x x' t) = (term124 _89578 _89597 _89598 P f x x' t).
Proof. exact (fun_ext (fun y : _89597 => @lem3456361 _89578 _89597 _89598 P f x y x' t)). Qed.
Lemma lem3456363 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456364 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term113 _89578 _89597 _89598 P f x x' t) = (term125 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456363 _89597) (@lem3456362 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456365 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : ((term112 _89578 _89597 _89598 P f x x' t) = (term113 _89578 _89597 _89598 P f x x' t)) = ((term108 _89578 _89597 _89598 P f x x' t) = (term125 _89578 _89597 _89598 P f x x' t)).
Proof. exact (MK_COMB (@lem3456356 _89578 _89597 _89598 P f x x' t) (@lem3456364 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456366 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term108 _89578 _89597 _89598 P f x x' t) = (term125 _89578 _89597 _89598 P f x x' t).
Proof. exact (EQ_MP (@lem3456365 _89578 _89597 _89598 P f x x' t) (@lem3456346 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456367 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term110 _89578 _89597 _89598 P f x t) = (term126 _89578 _89597 _89598 P f x t).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456366 _89578 _89597 _89598 P f x' x t)). Qed.
Lemma lem3456368 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456369 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term111 _89578 _89597 _89598 P f x t) = (term127 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456368 _89598) (@lem3456367 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456370 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term28 _89578 _89597 _89598 P f x t) = (term127 _89578 _89597 _89598 P f x t).
Proof. exact (TRANS (@lem3456342 _89578 _89597 _89598 P f x t) (@lem3456369 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456371 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term29 _89578 _89597 _89598 P f x) = (term128 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456370 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456372 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456373 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term30 _89578 _89597 _89598 P f x) = (term129 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456372 _89578) (@lem3456371 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456375 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term89 _89578 _89597 _89598 P f x) = (term130 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456374) (@lem3456373 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456376 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456377 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term91 _89578 _89597 _89598 P x f) = (term131 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456375 _89578 _89597 _89598 P f x) (@lem3456376 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456379 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3456380 {_89578 : Type'} (P : type686 _89578) (Q : Prop) : (term132 _89578 P Q) = (term133 _89578 P Q).
Proof. exact (@lem3456379 (_89578 -> Prop) P Q). Qed.
Lemma lem3456381 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term134 _89578 _89597 _89598 P x f) = (term135 _89578 _89597 _89598 P x f).
Proof. exact (@lem3456380 _89578 (term128 _89578 _89597 _89598 P f x) (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456382 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term136 _89578 _89597 _89598 P f x t) = (term127 _89578 _89597 _89598 P f x t).
Proof. exact (eq_refl (term136 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456383 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term137 _89578 _89597 _89598 P f x) = (term128 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456382 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456384 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456385 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term138 _89578 _89597 _89598 P f x) = (term129 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456384 _89578) (@lem3456383 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456387 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term139 _89578 _89597 _89598 P f x) = (term130 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456386) (@lem3456385 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456388 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456389 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term134 _89578 _89597 _89598 P x f) = (term131 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456387 _89578 _89597 _89598 P f x) (@lem3456388 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456391 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term140 _89578 _89597 _89598 P x f) = (term141 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456390) (@lem3456389 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456392 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term136 _89578 _89597 _89598 P f x t) = (term127 _89578 _89597 _89598 P f x t).
Proof. exact (eq_refl (term136 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456394 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term142 _89578 _89597 _89598 P f x t) = (term143 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456393) (@lem3456392 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456395 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456396 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term144 _89578 _89597 _89598 t P x f) = (term145 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456394 _89578 _89597 _89598 P f x t) (@lem3456395 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456397 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term146 _89578 _89597 _89598 P x f) = (term147 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456396 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456398 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456399 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term135 _89578 _89597 _89598 P x f) = (term148 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456398 _89578) (@lem3456397 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456400 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term134 _89578 _89597 _89598 P x f) = (term135 _89578 _89597 _89598 P x f)) = ((term131 _89578 _89597 _89598 P x f) = (term148 _89578 _89597 _89598 P x f)).
Proof. exact (MK_COMB (@lem3456391 _89578 _89597 _89598 P x f) (@lem3456399 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456401 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term131 _89578 _89597 _89598 P x f) = (term148 _89578 _89597 _89598 P x f).
Proof. exact (EQ_MP (@lem3456400 _89578 _89597 _89598 P x f) (@lem3456381 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456403 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3456404 {_89598 : Type'} (P : _89598 -> Prop) (Q : Prop) : (term96 _89598 P Q) = (term97 _89598 P Q).
Proof. exact (@lem3456403 _89598 P Q). Qed.
Lemma lem3456405 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term149 _89578 _89597 _89598 t P x f) = (term150 _89578 _89597 _89598 t P x f).
Proof. exact (@lem3456404 _89598 (term126 _89578 _89597 _89598 P f x t) (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456406 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term151 _89578 _89597 _89598 P f x' t x) = (term125 _89578 _89597 _89598 P f x x' t).
Proof. exact (eq_refl (term151 _89578 _89597 _89598 P f x' t x)). Qed.
Lemma lem3456407 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term152 _89578 _89597 _89598 P f x t) = (term126 _89578 _89597 _89598 P f x t).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456406 _89578 _89597 _89598 P f x' x t)). Qed.
Lemma lem3456408 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456409 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term153 _89578 _89597 _89598 P f x t) = (term127 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456408 _89598) (@lem3456407 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456411 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term154 _89578 _89597 _89598 P f x t) = (term143 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456410) (@lem3456409 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456412 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456413 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term149 _89578 _89597 _89598 t P x f) = (term145 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456411 _89578 _89597 _89598 P f x t) (@lem3456412 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456414 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456415 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term155 _89578 _89597 _89598 t P x f) = (term156 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456414) (@lem3456413 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456416 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term151 _89578 _89597 _89598 P f x' t x) = (term125 _89578 _89597 _89598 P f x x' t).
Proof. exact (eq_refl (term151 _89578 _89597 _89598 P f x' t x)). Qed.
Lemma lem3456417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456418 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term157 _89578 _89597 _89598 P f x' t x) = (term158 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456417) (@lem3456416 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456419 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456420 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term159 _89578 _89597 _89598 t x P x' f) = (term160 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456418 _89578 _89597 _89598 P f x x' t) (@lem3456419 _89578 _89597 _89598 P x' f)). Qed.
Lemma lem3456421 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term161 _89578 _89597 _89598 t P x f) = (term162 _89578 _89597 _89598 t P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456420 _89578 _89597 _89598 x' t P x f)). Qed.
Lemma lem3456422 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456423 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term150 _89578 _89597 _89598 t P x f) = (term163 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456422 _89598) (@lem3456421 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456424 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term149 _89578 _89597 _89598 t P x f) = (term150 _89578 _89597 _89598 t P x f)) = ((term145 _89578 _89597 _89598 t P x f) = (term163 _89578 _89597 _89598 t P x f)).
Proof. exact (MK_COMB (@lem3456415 _89578 _89597 _89598 t P x f) (@lem3456423 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456425 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term145 _89578 _89597 _89598 t P x f) = (term163 _89578 _89597 _89598 t P x f).
Proof. exact (EQ_MP (@lem3456424 _89578 _89597 _89598 t P x f) (@lem3456405 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456427 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3456428 {_89597 : Type'} (P : _89597 -> Prop) (Q : Prop) : (term96 _89597 P Q) = (term97 _89597 P Q).
Proof. exact (@lem3456427 _89597 P Q). Qed.
Lemma lem3456429 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term164 _89578 _89597 _89598 x t P x' f) = (term165 _89578 _89597 _89598 x t P x' f).
Proof. exact (@lem3456428 _89597 (term124 _89578 _89597 _89598 P f x x' t) (term84 _89578 _89597 _89598 P x' f)). Qed.
Lemma lem3456430 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) (x' : _89578) (t : _89578 -> Prop) : (term166 _89578 _89597 _89598 P f x x' t y) = (term122 _89578 _89597 _89598 P f x y x' t).
Proof. exact (eq_refl (term166 _89578 _89597 _89598 P f x x' t y)). Qed.
Lemma lem3456431 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term167 _89578 _89597 _89598 P f x x' t) = (term124 _89578 _89597 _89598 P f x x' t).
Proof. exact (fun_ext (fun y : _89597 => @lem3456430 _89578 _89597 _89598 P f x y x' t)). Qed.
Lemma lem3456432 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456433 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term168 _89578 _89597 _89598 P f x x' t) = (term125 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456432 _89597) (@lem3456431 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456434 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456435 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term169 _89578 _89597 _89598 P f x x' t) = (term158 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456434) (@lem3456433 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456436 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456437 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term164 _89578 _89597 _89598 x t P x' f) = (term160 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456435 _89578 _89597 _89598 P f x x' t) (@lem3456436 _89578 _89597 _89598 P x' f)). Qed.
Lemma lem3456438 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456439 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term170 _89578 _89597 _89598 x t P x' f) = (term171 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456438) (@lem3456437 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456440 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) (x' : _89578) (t : _89578 -> Prop) : (term166 _89578 _89597 _89598 P f x x' t y) = (term122 _89578 _89597 _89598 P f x y x' t).
Proof. exact (eq_refl (term166 _89578 _89597 _89598 P f x x' t y)). Qed.
Lemma lem3456441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456442 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) (x' : _89578) (t : _89578 -> Prop) : (term172 _89578 _89597 _89598 P f x x' t y) = (term173 _89578 _89597 _89598 P f x y x' t).
Proof. exact (MK_COMB (@lem3456441) (@lem3456440 _89578 _89597 _89598 P f x y x' t)). Qed.
Lemma lem3456443 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term84 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456444 {_89578 _89597 _89598 : Type'} (x : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term174 _89578 _89597 _89598 x t y P x' f) = (term175 _89578 _89597 _89598 x y t P x' f).
Proof. exact (MK_COMB (@lem3456442 _89578 _89597 _89598 P f x y x' t) (@lem3456443 _89578 _89597 _89598 P x' f)). Qed.
Lemma lem3456445 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term176 _89578 _89597 _89598 x t P x' f) = (term177 _89578 _89597 _89598 x t P x' f).
Proof. exact (fun_ext (fun y : _89597 => @lem3456444 _89578 _89597 _89598 x y t P x' f)). Qed.
Lemma lem3456446 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456447 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term165 _89578 _89597 _89598 x t P x' f) = (term178 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456446 _89597) (@lem3456445 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456448 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : ((term164 _89578 _89597 _89598 x t P x' f) = (term165 _89578 _89597 _89598 x t P x' f)) = ((term160 _89578 _89597 _89598 x t P x' f) = (term178 _89578 _89597 _89598 x t P x' f)).
Proof. exact (MK_COMB (@lem3456439 _89578 _89597 _89598 x t P x' f) (@lem3456447 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456449 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term160 _89578 _89597 _89598 x t P x' f) = (term178 _89578 _89597 _89598 x t P x' f).
Proof. exact (EQ_MP (@lem3456448 _89578 _89597 _89598 x t P x' f) (@lem3456429 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456450 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term162 _89578 _89597 _89598 t P x f) = (term179 _89578 _89597 _89598 t P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456449 _89578 _89597 _89598 x' t P x f)). Qed.
Lemma lem3456451 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456452 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term163 _89578 _89597 _89598 t P x f) = (term180 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456451 _89598) (@lem3456450 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456453 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term145 _89578 _89597 _89598 t P x f) = (term180 _89578 _89597 _89598 t P x f).
Proof. exact (TRANS (@lem3456425 _89578 _89597 _89598 t P x f) (@lem3456452 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456454 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term147 _89578 _89597 _89598 P x f) = (term181 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456453 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456455 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456456 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term148 _89578 _89597 _89598 P x f) = (term182 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456455 _89578) (@lem3456454 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456457 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term131 _89578 _89597 _89598 P x f) = (term182 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456401 _89578 _89597 _89598 P x f) (@lem3456456 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456458 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term91 _89578 _89597 _89598 P x f) = (term182 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456377 _89578 _89597 _89598 P x f) (@lem3456457 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456460 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term93 _89578 _89597 _89598 P x f) = (term183 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456459) (@lem3456458 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456462 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3456463 {_89598 : Type'} (P : Prop) (Q : _89598 -> Prop) : (term184 _89598 P Q) = (term185 _89598 P Q).
Proof. exact (@lem3456462 _89598 P Q). Qed.
Lemma lem3456464 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term186 _89578 _89597 _89598 P x f) = (term187 _89578 _89597 _89598 P x f).
Proof. exact (@lem3456463 _89598 (term67 _89578 _89597 _89598 P f x) (term20 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456465 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term80 _89578 _89597 _89598 P x f x') = (term19 _89578 _89597 _89598 P x f x').
Proof. exact (eq_refl (term80 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456466 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term188 _89578 _89597 _89598 P x f) = (term20 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456465 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456467 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456468 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term189 _89578 _89597 _89598 P x f) = (term21 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456467 _89598) (@lem3456466 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456469 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term86 _89578 _89597 _89598 P f x) = (term86 _89578 _89597 _89598 P f x).
Proof. exact (eq_refl (term86 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456470 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term186 _89578 _89597 _89598 P x f) = (term88 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456469 _89578 _89597 _89598 P f x) (@lem3456468 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456471 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456472 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term190 _89578 _89597 _89598 P x f) = (term191 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456471) (@lem3456470 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456473 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term80 _89578 _89597 _89598 P x f x') = (term19 _89578 _89597 _89598 P x f x').
Proof. exact (eq_refl (term80 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456474 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term86 _89578 _89597 _89598 P f x) = (term86 _89578 _89597 _89598 P f x).
Proof. exact (eq_refl (term86 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456475 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term192 _89578 _89597 _89598 P x f x') = (term193 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456474 _89578 _89597 _89598 P f x) (@lem3456473 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456476 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term194 _89578 _89597 _89598 P x f) = (term195 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456475 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456477 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456478 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term187 _89578 _89597 _89598 P x f) = (term196 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456477 _89598) (@lem3456476 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456479 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term186 _89578 _89597 _89598 P x f) = (term187 _89578 _89597 _89598 P x f)) = ((term88 _89578 _89597 _89598 P x f) = (term196 _89578 _89597 _89598 P x f)).
Proof. exact (MK_COMB (@lem3456472 _89578 _89597 _89598 P x f) (@lem3456478 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456480 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term88 _89578 _89597 _89598 P x f) = (term196 _89578 _89597 _89598 P x f).
Proof. exact (EQ_MP (@lem3456479 _89578 _89597 _89598 P x f) (@lem3456464 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456482 {A : Type'} (P : Prop) (Q : A -> Prop) : (term184 A P Q) = (term185 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3456483 {_89597 : Type'} (P : Prop) (Q : _89597 -> Prop) : (term184 _89597 P Q) = (term185 _89597 P Q).
Proof. exact (@lem3456482 _89597 P Q). Qed.
Lemma lem3456484 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term197 _89578 _89597 _89598 P x f x') = (term198 _89578 _89597 _89598 P x f x').
Proof. exact (@lem3456483 _89597 (term67 _89578 _89597 _89598 P f x) (term18 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456485 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term73 _89578 _89597 _89598 P x f x' y) = (term17 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term73 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456486 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term199 _89578 _89597 _89598 P x f x') = (term18 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3456485 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456487 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456488 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term200 _89578 _89597 _89598 P x f x') = (term19 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456487 _89597) (@lem3456486 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456489 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term86 _89578 _89597 _89598 P f x) = (term86 _89578 _89597 _89598 P f x).
Proof. exact (eq_refl (term86 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456490 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term197 _89578 _89597 _89598 P x f x') = (term193 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456489 _89578 _89597 _89598 P f x) (@lem3456488 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456491 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456492 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term201 _89578 _89597 _89598 P x f x') = (term202 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456491) (@lem3456490 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456493 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term73 _89578 _89597 _89598 P x f x' y) = (term17 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term73 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456494 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term86 _89578 _89597 _89598 P f x) = (term86 _89578 _89597 _89598 P f x).
Proof. exact (eq_refl (term86 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456495 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term203 _89578 _89597 _89598 P x f x' y) = (term204 _89578 _89597 _89598 P x f x' y).
Proof. exact (MK_COMB (@lem3456494 _89578 _89597 _89598 P f x) (@lem3456493 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456496 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term205 _89578 _89597 _89598 P x f x') = (term206 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3456495 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456497 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456498 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term198 _89578 _89597 _89598 P x f x') = (term207 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456497 _89597) (@lem3456496 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456499 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : ((term197 _89578 _89597 _89598 P x f x') = (term198 _89578 _89597 _89598 P x f x')) = ((term193 _89578 _89597 _89598 P x f x') = (term207 _89578 _89597 _89598 P x f x')).
Proof. exact (MK_COMB (@lem3456492 _89578 _89597 _89598 P x f x') (@lem3456498 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456500 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term193 _89578 _89597 _89598 P x f x') = (term207 _89578 _89597 _89598 P x f x').
Proof. exact (EQ_MP (@lem3456499 _89578 _89597 _89598 P x f x') (@lem3456484 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456501 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term195 _89578 _89597 _89598 P x f) = (term208 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456500 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456502 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456503 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term196 _89578 _89597 _89598 P x f) = (term209 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456502 _89598) (@lem3456501 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456504 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term88 _89578 _89597 _89598 P x f) = (term209 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456480 _89578 _89597 _89598 P x f) (@lem3456503 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456505 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term95 _89578 _89597 _89598 P x f) = (term210 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456460 _89578 _89597 _89598 P x f) (@lem3456504 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456509 {A : Type'} (P : A -> Prop) (Q : Prop) : (term211 A P Q) = (term212 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3456510 {_89578 : Type'} (P : type686 _89578) (Q : Prop) : (term213 _89578 P Q) = (term214 _89578 P Q).
Proof. exact (@lem3456509 (_89578 -> Prop) P Q). Qed.
Lemma lem3456511 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term215 _89578 _89597 _89598 P x f) = (term216 _89578 _89597 _89598 P x f).
Proof. exact (@lem3456510 _89578 (term181 _89578 _89597 _89598 P x f) (term209 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456512 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term217 _89578 _89597 _89598 P x f t) = (term180 _89578 _89597 _89598 t P x f).
Proof. exact (eq_refl (term217 _89578 _89597 _89598 P x f t)). Qed.
Lemma lem3456513 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term218 _89578 _89597 _89598 P x f) = (term181 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456512 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456514 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456515 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term219 _89578 _89597 _89598 P x f) = (term182 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456514 _89578) (@lem3456513 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456516 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456517 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term220 _89578 _89597 _89598 P x f) = (term183 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456516) (@lem3456515 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456518 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term209 _89578 _89597 _89598 P x f) = (term209 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term209 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456519 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term215 _89578 _89597 _89598 P x f) = (term210 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456517 _89578 _89597 _89598 P x f) (@lem3456518 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456521 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term221 _89578 _89597 _89598 P x f) = (term222 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456520) (@lem3456519 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456522 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term217 _89578 _89597 _89598 P x f t) = (term180 _89578 _89597 _89598 t P x f).
Proof. exact (eq_refl (term217 _89578 _89597 _89598 P x f t)). Qed.
Lemma lem3456523 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456524 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term223 _89578 _89597 _89598 P x f t) = (term224 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456523) (@lem3456522 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456525 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term209 _89578 _89597 _89598 P x f) = (term209 _89578 _89597 _89598 P x f).
Proof. exact (eq_refl (term209 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456526 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term225 _89578 _89597 _89598 t P x f) = (term226 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456524 _89578 _89597 _89598 t P x f) (@lem3456525 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456527 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term227 _89578 _89597 _89598 P x f) = (term228 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456526 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456528 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456529 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term216 _89578 _89597 _89598 P x f) = (term229 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456528 _89578) (@lem3456527 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456530 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term215 _89578 _89597 _89598 P x f) = (term216 _89578 _89597 _89598 P x f)) = ((term210 _89578 _89597 _89598 P x f) = (term229 _89578 _89597 _89598 P x f)).
Proof. exact (MK_COMB (@lem3456521 _89578 _89597 _89598 P x f) (@lem3456529 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456531 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term210 _89578 _89597 _89598 P x f) = (term229 _89578 _89597 _89598 P x f).
Proof. exact (EQ_MP (@lem3456530 _89578 _89597 _89598 P x f) (@lem3456511 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456533 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3456534 {_89598 : Type'} (P : _89598 -> Prop) (Q : _89598 -> Prop) : (term230 _89598 P Q) = (term231 _89598 P Q).
Proof. exact (@lem3456533 _89598 P Q). Qed.
Lemma lem3456535 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term232 _89578 _89597 _89598 t P x f) = (term233 _89578 _89597 _89598 t P x f).
Proof. exact (@lem3456534 _89598 (term179 _89578 _89597 _89598 t P x f) (term208 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456536 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term234 _89578 _89597 _89598 t P x' f x) = (term178 _89578 _89597 _89598 x t P x' f).
Proof. exact (eq_refl (term234 _89578 _89597 _89598 t P x' f x)). Qed.
Lemma lem3456537 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term235 _89578 _89597 _89598 t P x f) = (term179 _89578 _89597 _89598 t P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456536 _89578 _89597 _89598 x' t P x f)). Qed.
Lemma lem3456538 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456539 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term236 _89578 _89597 _89598 t P x f) = (term180 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456538 _89598) (@lem3456537 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456540 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456541 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term237 _89578 _89597 _89598 t P x f) = (term224 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456540) (@lem3456539 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456542 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term238 _89578 _89597 _89598 P x f x') = (term207 _89578 _89597 _89598 P x f x').
Proof. exact (eq_refl (term238 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456543 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term239 _89578 _89597 _89598 P x f) = (term208 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456542 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456544 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456545 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term240 _89578 _89597 _89598 P x f) = (term209 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456544 _89598) (@lem3456543 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456546 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term232 _89578 _89597 _89598 t P x f) = (term226 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456541 _89578 _89597 _89598 t P x f) (@lem3456545 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456547 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456548 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term241 _89578 _89597 _89598 t P x f) = (term242 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456547) (@lem3456546 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456549 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term234 _89578 _89597 _89598 t P x' f x) = (term178 _89578 _89597 _89598 x t P x' f).
Proof. exact (eq_refl (term234 _89578 _89597 _89598 t P x' f x)). Qed.
Lemma lem3456550 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456551 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term243 _89578 _89597 _89598 t P x' f x) = (term244 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456550) (@lem3456549 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456552 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term238 _89578 _89597 _89598 P x f x') = (term207 _89578 _89597 _89598 P x f x').
Proof. exact (eq_refl (term238 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456553 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term245 _89578 _89597 _89598 t P x f x') = (term246 _89578 _89597 _89598 t P x f x').
Proof. exact (MK_COMB (@lem3456551 _89578 _89597 _89598 x' t P x f) (@lem3456552 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456554 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term247 _89578 _89597 _89598 t P x f) = (term248 _89578 _89597 _89598 t P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456553 _89578 _89597 _89598 t P x f x')). Qed.
Lemma lem3456555 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456556 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term233 _89578 _89597 _89598 t P x f) = (term249 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456555 _89598) (@lem3456554 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456557 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : ((term232 _89578 _89597 _89598 t P x f) = (term233 _89578 _89597 _89598 t P x f)) = ((term226 _89578 _89597 _89598 t P x f) = (term249 _89578 _89597 _89598 t P x f)).
Proof. exact (MK_COMB (@lem3456548 _89578 _89597 _89598 t P x f) (@lem3456556 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456558 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term226 _89578 _89597 _89598 t P x f) = (term249 _89578 _89597 _89598 t P x f).
Proof. exact (EQ_MP (@lem3456557 _89578 _89597 _89598 t P x f) (@lem3456535 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456560 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term230 A P Q) = (term231 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3456561 {_89597 : Type'} (P : _89597 -> Prop) (Q : _89597 -> Prop) : (term230 _89597 P Q) = (term231 _89597 P Q).
Proof. exact (@lem3456560 _89597 P Q). Qed.
Lemma lem3456562 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term250 _89578 _89597 _89598 t P x f x') = (term251 _89578 _89597 _89598 t P x f x').
Proof. exact (@lem3456561 _89597 (term177 _89578 _89597 _89598 x' t P x f) (term206 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456563 {_89578 _89597 _89598 : Type'} (x : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term252 _89578 _89597 _89598 x t P x' f y) = (term175 _89578 _89597 _89598 x y t P x' f).
Proof. exact (eq_refl (term252 _89578 _89597 _89598 x t P x' f y)). Qed.
Lemma lem3456564 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term253 _89578 _89597 _89598 x t P x' f) = (term177 _89578 _89597 _89598 x t P x' f).
Proof. exact (fun_ext (fun y : _89597 => @lem3456563 _89578 _89597 _89598 x y t P x' f)). Qed.
Lemma lem3456565 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456566 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term254 _89578 _89597 _89598 x t P x' f) = (term178 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456565 _89597) (@lem3456564 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456567 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456568 {_89578 _89597 _89598 : Type'} (x : _89598) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term255 _89578 _89597 _89598 x t P x' f) = (term244 _89578 _89597 _89598 x t P x' f).
Proof. exact (MK_COMB (@lem3456567) (@lem3456566 _89578 _89597 _89598 x t P x' f)). Qed.
Lemma lem3456569 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term256 _89578 _89597 _89598 P x f x' y) = (term204 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term256 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456570 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term257 _89578 _89597 _89598 P x f x') = (term206 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3456569 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456571 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456572 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term258 _89578 _89597 _89598 P x f x') = (term207 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456571 _89597) (@lem3456570 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456573 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term250 _89578 _89597 _89598 t P x f x') = (term246 _89578 _89597 _89598 t P x f x').
Proof. exact (MK_COMB (@lem3456568 _89578 _89597 _89598 x' t P x f) (@lem3456572 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456574 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456575 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term259 _89578 _89597 _89598 t P x f x') = (term260 _89578 _89597 _89598 t P x f x').
Proof. exact (MK_COMB (@lem3456574) (@lem3456573 _89578 _89597 _89598 t P x f x')). Qed.
Lemma lem3456576 {_89578 _89597 _89598 : Type'} (x : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term252 _89578 _89597 _89598 x t P x' f y) = (term175 _89578 _89597 _89598 x y t P x' f).
Proof. exact (eq_refl (term252 _89578 _89597 _89598 x t P x' f y)). Qed.
Lemma lem3456577 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456578 {_89578 _89597 _89598 : Type'} (x : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x' : _89578) (f : type1517 _89578 _89597 _89598) : (term261 _89578 _89597 _89598 x t P x' f y) = (term262 _89578 _89597 _89598 x y t P x' f).
Proof. exact (MK_COMB (@lem3456577) (@lem3456576 _89578 _89597 _89598 x y t P x' f)). Qed.
Lemma lem3456579 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term256 _89578 _89597 _89598 P x f x' y) = (term204 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term256 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456580 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term263 _89578 _89597 _89598 t P x f x' y) = (term264 _89578 _89597 _89598 t P x f x' y).
Proof. exact (MK_COMB (@lem3456578 _89578 _89597 _89598 x' y t P x f) (@lem3456579 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456581 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term265 _89578 _89597 _89598 t P x f x') = (term266 _89578 _89597 _89598 t P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3456580 _89578 _89597 _89598 t P x f x' y)). Qed.
Lemma lem3456582 {_89597 : Type'} : (@ex _89597) = (@ex _89597).
Proof. exact (eq_refl (@ex _89597)). Qed.
Lemma lem3456583 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term251 _89578 _89597 _89598 t P x f x') = (term267 _89578 _89597 _89598 t P x f x').
Proof. exact (MK_COMB (@lem3456582 _89597) (@lem3456581 _89578 _89597 _89598 t P x f x')). Qed.
Lemma lem3456584 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : ((term250 _89578 _89597 _89598 t P x f x') = (term251 _89578 _89597 _89598 t P x f x')) = ((term246 _89578 _89597 _89598 t P x f x') = (term267 _89578 _89597 _89598 t P x f x')).
Proof. exact (MK_COMB (@lem3456575 _89578 _89597 _89598 t P x f x') (@lem3456583 _89578 _89597 _89598 t P x f x')). Qed.
Lemma lem3456585 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term246 _89578 _89597 _89598 t P x f x') = (term267 _89578 _89597 _89598 t P x f x').
Proof. exact (EQ_MP (@lem3456584 _89578 _89597 _89598 t P x f x') (@lem3456562 _89578 _89597 _89598 t P x f x')). Qed.
Lemma lem3456586 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term248 _89578 _89597 _89598 t P x f) = (term268 _89578 _89597 _89598 t P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456585 _89578 _89597 _89598 t P x f x')). Qed.
Lemma lem3456587 {_89598 : Type'} : (@ex _89598) = (@ex _89598).
Proof. exact (eq_refl (@ex _89598)). Qed.
Lemma lem3456588 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term249 _89578 _89597 _89598 t P x f) = (term269 _89578 _89597 _89598 t P x f).
Proof. exact (MK_COMB (@lem3456587 _89598) (@lem3456586 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456589 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term226 _89578 _89597 _89598 t P x f) = (term269 _89578 _89597 _89598 t P x f).
Proof. exact (TRANS (@lem3456558 _89578 _89597 _89598 t P x f) (@lem3456588 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456590 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term228 _89578 _89597 _89598 P x f) = (term270 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456589 _89578 _89597 _89598 t P x f)). Qed.
Lemma lem3456591 {_89578 : Type'} : (@ex (_89578 -> Prop)) = (@ex (_89578 -> Prop)).
Proof. exact (eq_refl (@ex (_89578 -> Prop))). Qed.
Lemma lem3456592 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term229 _89578 _89597 _89598 P x f) = (term271 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456591 _89578) (@lem3456590 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456593 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term210 _89578 _89597 _89598 P x f) = (term271 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456531 _89578 _89597 _89598 P x f) (@lem3456592 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456595 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term95 _89578 _89597 _89598 P x f) = (term271 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456505 _89578 _89597 _89598 P x f) (@lem3456593 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456596 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term34 _89578 _89597 _89598 P x f) = (term271 _89578 _89597 _89598 P x f).
Proof. exact (TRANS (@lem3456013 _89578 _89597 _89598 P x f) (@lem3456595 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456597 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term34 _89578 _89597 _89598 P x f) : term271 _89578 _89597 _89598 P x f.
Proof. exact (EQ_MP (@lem3456596 _89578 _89597 _89598 P x f) (@lem3455903 _89578 _89597 _89598 P x f h1)). Qed.
Lemma lem3456598 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term269 _89578 _89597 _89598 t P x f) : term269 _89578 _89597 _89598 t P x f.
Proof. exact (h1). Qed.
Lemma lem3456599 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (h1 : term267 _89578 _89597 _89598 t P x f x') : term267 _89578 _89597 _89598 t P x f x'.
Proof. exact (h1). Qed.
Lemma lem3456600 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term264 _89578 _89597 _89598 t P x f x' y) : term264 _89578 _89597 _89598 t P x f x' y.
Proof. exact (h1). Qed.
Lemma lem3456617 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term17 _89578 _89597 _89598 P x f x' y) = (term17 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term17 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456624 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term53 _89578 x t) = (term53 _89578 x t).
Proof. exact (eq_refl (term53 _89578 x t)). Qed.
Lemma lem3456645 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term36 _89578 _89597 _89598 P t f x y) = (term36 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term36 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456646 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term44 _89578 _89597 _89598 P t f x) = (term44 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3456645 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456647 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3456648 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term45 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456647 _89597) (@lem3456646 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456649 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term51 _89578 _89597 _89598 P t f) = (term51 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3456648 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456650 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456651 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term52 _89578 _89597 _89598 P t f) = (term52 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3456650 _89598) (@lem3456649 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3456652 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456653 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term55 _89578 _89597 _89598 P t f) = (term55 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3456652) (@lem3456651 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3456654 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term57 _89578 _89597 _89598 P f x t) = (term57 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456653 _89578 _89597 _89598 P t f) (@lem3456624 _89578 x t)). Qed.
Lemma lem3456655 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term66 _89578 _89597 _89598 P f x) = (term66 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456654 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456656 {_89578 : Type'} : (@all (_89578 -> Prop)) = (@all (_89578 -> Prop)).
Proof. exact (eq_refl (@all (_89578 -> Prop))). Qed.
Lemma lem3456657 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term67 _89578 _89597 _89598 P f x) = (term67 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456656 _89578) (@lem3456655 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456658 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3456659 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term86 _89578 _89597 _89598 P f x) = (term86 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456658) (@lem3456657 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456660 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term204 _89578 _89597 _89598 P x f x' y) = (term204 _89578 _89597 _89598 P x f x' y).
Proof. exact (MK_COMB (@lem3456659 _89578 _89597 _89598 P f x) (@lem3456617 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456681 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term69 _89578 _89597 _89598 P x f x' y) = (term69 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term69 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456682 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term76 _89578 _89597 _89598 P x f x') = (term76 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3456681 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456683 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3456684 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term77 _89578 _89597 _89598 P x f x') = (term77 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456683 _89597) (@lem3456682 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456685 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term83 _89578 _89597 _89598 P x f) = (term83 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456684 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456686 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456687 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456686 _89598) (@lem3456685 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456714 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (x : _89578) (t : _89578 -> Prop) : (term173 _89578 _89597 _89598 P f x' y x t) = (term173 _89578 _89597 _89598 P f x' y x t).
Proof. exact (eq_refl (term173 _89578 _89597 _89598 P f x' y x t)). Qed.
Lemma lem3456715 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term175 _89578 _89597 _89598 x' y t P x f) = (term175 _89578 _89597 _89598 x' y t P x f).
Proof. exact (MK_COMB (@lem3456714 _89578 _89597 _89598 P f x' y x t) (@lem3456687 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456717 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term262 _89578 _89597 _89598 x' y t P x f) = (term262 _89578 _89597 _89598 x' y t P x f).
Proof. exact (MK_COMB (@lem3456716) (@lem3456715 _89578 _89597 _89598 x' y t P x f)). Qed.
Lemma lem3456718 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term264 _89578 _89597 _89598 t P x f x' y) = (term264 _89578 _89597 _89598 t P x f x' y).
Proof. exact (MK_COMB (@lem3456717 _89578 _89597 _89598 x' y t P x f) (@lem3456660 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456719 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term264 _89578 _89597 _89598 t P x f x' y) : term264 _89578 _89597 _89598 t P x f x' y.
Proof. exact (EQ_MP (@lem3456718 _89578 _89597 _89598 t P x f x' y) (@lem3456600 _89578 _89597 _89598 t P x f x' y h1)). Qed.
Lemma lem3456720 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term175 _89578 _89597 _89598 x' y t P x f.
Proof. exact (h1). Qed.
Lemma lem3456721 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term204 _89578 _89597 _89598 P x f x' y.
Proof. exact (h1). Qed.
Lemma lem3456722 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term84 _89578 _89597 _89598 P x f.
Proof. exact (proj2 (@lem3456720 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456723 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term122 _89578 _89597 _89598 P f x' y x t.
Proof. exact (proj1 (@lem3456720 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456725 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term22 _89578 _89597 _89598 P t f x' y.
Proof. exact (proj1 (@lem3456723 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456728 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term17 _89578 _89597 _89598 P x f x' y.
Proof. exact (proj2 (@lem3456721 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3456729 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term67 _89578 _89597 _89598 P f x.
Proof. exact (proj1 (@lem3456721 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3456739 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term69 _89578 _89597 _89598 P x f x' y) = (term69 _89578 _89597 _89598 P x f x' y).
Proof. exact (eq_refl (term69 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456740 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term76 _89578 _89597 _89598 P x f x') = (term76 _89578 _89597 _89598 P x f x').
Proof. exact (fun_ext (fun y : _89597 => @lem3456739 _89578 _89597 _89598 P x f x' y)). Qed.
Lemma lem3456741 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3456742 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) : (term77 _89578 _89597 _89598 P x f x') = (term77 _89578 _89597 _89598 P x f x').
Proof. exact (MK_COMB (@lem3456741 _89597) (@lem3456740 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456743 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term83 _89578 _89597 _89598 P x f) = (term83 _89578 _89597 _89598 P x f).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456742 _89578 _89597 _89598 P x f x')). Qed.
Lemma lem3456744 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456746 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term84 _89578 _89597 _89598 P x f) = (term84 _89578 _89597 _89598 P x f).
Proof. exact (MK_COMB (@lem3456744 _89598) (@lem3456743 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3456747 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term84 _89578 _89597 _89598 P x f.
Proof. exact (EQ_MP (@lem3456746 _89578 _89597 _89598 P x f) (@lem3456722 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456761 {A : Type'} (P : A -> Prop) (Q : Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3456762 {_89598 : Type'} (P : _89598 -> Prop) (Q : Prop) : (term272 _89598 P Q) = (term273 _89598 P Q).
Proof. exact (@lem3456761 _89598 P Q). Qed.
Lemma lem3456763 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term274 _89578 _89597 _89598 P f x t) = (term275 _89578 _89597 _89598 P f x t).
Proof. exact (@lem3456762 _89598 (term51 _89578 _89597 _89598 P t f) (term53 _89578 x t)). Qed.
Lemma lem3456764 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term276 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (eq_refl (term276 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456765 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term277 _89578 _89597 _89598 P t f) = (term51 _89578 _89597 _89598 P t f).
Proof. exact (fun_ext (fun x : _89598 => @lem3456764 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456766 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456767 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term278 _89578 _89597 _89598 P t f) = (term52 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3456766 _89598) (@lem3456765 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3456768 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456769 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) : (term279 _89578 _89597 _89598 P t f) = (term55 _89578 _89597 _89598 P t f).
Proof. exact (MK_COMB (@lem3456768) (@lem3456767 _89578 _89597 _89598 P t f)). Qed.
Lemma lem3456770 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term53 _89578 x t) = (term53 _89578 x t).
Proof. exact (eq_refl (term53 _89578 x t)). Qed.
Lemma lem3456771 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term274 _89578 _89597 _89598 P f x t) = (term57 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456769 _89578 _89597 _89598 P t f) (@lem3456770 _89578 x t)). Qed.
Lemma lem3456772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456773 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term280 _89578 _89597 _89598 P f x t) = (term281 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456772) (@lem3456771 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456774 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term276 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (eq_refl (term276 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456775 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456776 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term282 _89578 _89597 _89598 P t f x) = (term283 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456775) (@lem3456774 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456777 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term53 _89578 x t) = (term53 _89578 x t).
Proof. exact (eq_refl (term53 _89578 x t)). Qed.
Lemma lem3456778 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term284 _89578 _89597 _89598 P f x x' t) = (term285 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456776 _89578 _89597 _89598 P t f x) (@lem3456777 _89578 x' t)). Qed.
Lemma lem3456779 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term286 _89578 _89597 _89598 P f x t) = (term287 _89578 _89597 _89598 P f x t).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456778 _89578 _89597 _89598 P f x' x t)). Qed.
Lemma lem3456780 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456781 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term275 _89578 _89597 _89598 P f x t) = (term288 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456780 _89598) (@lem3456779 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456782 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : ((term274 _89578 _89597 _89598 P f x t) = (term275 _89578 _89597 _89598 P f x t)) = ((term57 _89578 _89597 _89598 P f x t) = (term288 _89578 _89597 _89598 P f x t)).
Proof. exact (MK_COMB (@lem3456773 _89578 _89597 _89598 P f x t) (@lem3456781 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456783 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term57 _89578 _89597 _89598 P f x t) = (term288 _89578 _89597 _89598 P f x t).
Proof. exact (EQ_MP (@lem3456782 _89578 _89597 _89598 P f x t) (@lem3456763 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456785 {A : Type'} (P : A -> Prop) (Q : Prop) : (term272 A P Q) = (term273 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3456786 {_89597 : Type'} (P : _89597 -> Prop) (Q : Prop) : (term272 _89597 P Q) = (term273 _89597 P Q).
Proof. exact (@lem3456785 _89597 P Q). Qed.
Lemma lem3456787 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term289 _89578 _89597 _89598 P f x x' t) = (term290 _89578 _89597 _89598 P f x x' t).
Proof. exact (@lem3456786 _89597 (term44 _89578 _89597 _89598 P t f x) (term53 _89578 x' t)). Qed.
Lemma lem3456788 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term291 _89578 _89597 _89598 P t f x y) = (term36 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term291 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456789 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term292 _89578 _89597 _89598 P t f x) = (term44 _89578 _89597 _89598 P t f x).
Proof. exact (fun_ext (fun y : _89597 => @lem3456788 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456790 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3456791 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term293 _89578 _89597 _89598 P t f x) = (term45 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456790 _89597) (@lem3456789 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456792 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456793 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) : (term294 _89578 _89597 _89598 P t f x) = (term283 _89578 _89597 _89598 P t f x).
Proof. exact (MK_COMB (@lem3456792) (@lem3456791 _89578 _89597 _89598 P t f x)). Qed.
Lemma lem3456794 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term53 _89578 x t) = (term53 _89578 x t).
Proof. exact (eq_refl (term53 _89578 x t)). Qed.
Lemma lem3456795 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term289 _89578 _89597 _89598 P f x x' t) = (term285 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456793 _89578 _89597 _89598 P t f x) (@lem3456794 _89578 x' t)). Qed.
Lemma lem3456796 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456797 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term295 _89578 _89597 _89598 P f x x' t) = (term296 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456796) (@lem3456795 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456798 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term291 _89578 _89597 _89598 P t f x y) = (term36 _89578 _89597 _89598 P t f x y).
Proof. exact (eq_refl (term291 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456799 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3456800 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (t : _89578 -> Prop) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) : (term297 _89578 _89597 _89598 P t f x y) = (term298 _89578 _89597 _89598 P t f x y).
Proof. exact (MK_COMB (@lem3456799) (@lem3456798 _89578 _89597 _89598 P t f x y)). Qed.
Lemma lem3456801 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term53 _89578 x t) = (term53 _89578 x t).
Proof. exact (eq_refl (term53 _89578 x t)). Qed.
Lemma lem3456802 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) (x' : _89578) (t : _89578 -> Prop) : (term299 _89578 _89597 _89598 P f x y x' t) = (term300 _89578 _89597 _89598 P f x y x' t).
Proof. exact (MK_COMB (@lem3456800 _89578 _89597 _89598 P t f x y) (@lem3456801 _89578 x' t)). Qed.
Lemma lem3456803 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term301 _89578 _89597 _89598 P f x x' t) = (term302 _89578 _89597 _89598 P f x x' t).
Proof. exact (fun_ext (fun y : _89597 => @lem3456802 _89578 _89597 _89598 P f x y x' t)). Qed.
Lemma lem3456804 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3456805 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term290 _89578 _89597 _89598 P f x x' t) = (term303 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456804 _89597) (@lem3456803 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456806 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : ((term289 _89578 _89597 _89598 P f x x' t) = (term290 _89578 _89597 _89598 P f x x' t)) = ((term285 _89578 _89597 _89598 P f x x' t) = (term303 _89578 _89597 _89598 P f x x' t)).
Proof. exact (MK_COMB (@lem3456797 _89578 _89597 _89598 P f x x' t) (@lem3456805 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456807 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term285 _89578 _89597 _89598 P f x x' t) = (term303 _89578 _89597 _89598 P f x x' t).
Proof. exact (EQ_MP (@lem3456806 _89578 _89597 _89598 P f x x' t) (@lem3456787 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456808 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term287 _89578 _89597 _89598 P f x t) = (term304 _89578 _89597 _89598 P f x t).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456807 _89578 _89597 _89598 P f x' x t)). Qed.
Lemma lem3456809 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456810 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term288 _89578 _89597 _89598 P f x t) = (term305 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456809 _89598) (@lem3456808 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456811 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term57 _89578 _89597 _89598 P f x t) = (term305 _89578 _89597 _89598 P f x t).
Proof. exact (TRANS (@lem3456783 _89578 _89597 _89598 P f x t) (@lem3456810 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456812 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term66 _89578 _89597 _89598 P f x) = (term306 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456811 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456813 {_89578 : Type'} : (@all (_89578 -> Prop)) = (@all (_89578 -> Prop)).
Proof. exact (eq_refl (@all (_89578 -> Prop))). Qed.
Lemma lem3456814 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term67 _89578 _89597 _89598 P f x) = (term307 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456813 _89578) (@lem3456812 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456827 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (y : _89597) (x' : _89578) (t : _89578 -> Prop) : (term300 _89578 _89597 _89598 P f x y x' t) = (term300 _89578 _89597 _89598 P f x y x' t).
Proof. exact (eq_refl (term300 _89578 _89597 _89598 P f x y x' t)). Qed.
Lemma lem3456828 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term302 _89578 _89597 _89598 P f x x' t) = (term302 _89578 _89597 _89598 P f x x' t).
Proof. exact (fun_ext (fun y : _89597 => @lem3456827 _89578 _89597 _89598 P f x y x' t)). Qed.
Lemma lem3456829 {_89597 : Type'} : (@all _89597) = (@all _89597).
Proof. exact (eq_refl (@all _89597)). Qed.
Lemma lem3456830 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89598) (x' : _89578) (t : _89578 -> Prop) : (term303 _89578 _89597 _89598 P f x x' t) = (term303 _89578 _89597 _89598 P f x x' t).
Proof. exact (MK_COMB (@lem3456829 _89597) (@lem3456828 _89578 _89597 _89598 P f x x' t)). Qed.
Lemma lem3456831 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term304 _89578 _89597 _89598 P f x t) = (term304 _89578 _89597 _89598 P f x t).
Proof. exact (fun_ext (fun x' : _89598 => @lem3456830 _89578 _89597 _89598 P f x' x t)). Qed.
Lemma lem3456832 {_89598 : Type'} : (@all _89598) = (@all _89598).
Proof. exact (eq_refl (@all _89598)). Qed.
Lemma lem3456833 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (t : _89578 -> Prop) : (term305 _89578 _89597 _89598 P f x t) = (term305 _89578 _89597 _89598 P f x t).
Proof. exact (MK_COMB (@lem3456832 _89598) (@lem3456831 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456834 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term306 _89578 _89597 _89598 P f x) = (term306 _89578 _89597 _89598 P f x).
Proof. exact (fun_ext (fun t : _89578 -> Prop => @lem3456833 _89578 _89597 _89598 P f x t)). Qed.
Lemma lem3456835 {_89578 : Type'} : (@all (_89578 -> Prop)) = (@all (_89578 -> Prop)).
Proof. exact (eq_refl (@all (_89578 -> Prop))). Qed.
Lemma lem3456836 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term307 _89578 _89597 _89598 P f x) = (term307 _89578 _89597 _89598 P f x).
Proof. exact (MK_COMB (@lem3456835 _89578) (@lem3456834 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456837 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) : (term67 _89578 _89597 _89598 P f x) = (term307 _89578 _89597 _89598 P f x).
Proof. exact (TRANS (@lem3456814 _89578 _89597 _89598 P f x) (@lem3456836 _89578 _89597 _89598 P f x)). Qed.
Lemma lem3456838 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term307 _89578 _89597 _89598 P f x.
Proof. exact (EQ_MP (@lem3456837 _89578 _89597 _89598 P f x) (@lem3456729 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3456847 {_89578 _89597 _89598 : Type'} (_36458 : _89598) (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term308 _89578 _89597 _89598 P x f _36458.
Proof. exact (@lem3456747 _89578 _89597 _89598 x' y t P x f h1 _36458). Qed.
Lemma lem3456848 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (_36458 : _89598) : (term308 _89578 _89597 _89598 P x f _36458) = (term77 _89578 _89597 _89598 P x f _36458).
Proof. exact (eq_refl (term308 _89578 _89597 _89598 P x f _36458)). Qed.
Lemma lem3456849 {_89578 _89597 _89598 : Type'} (_36458 : _89598) (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term77 _89578 _89597 _89598 P x f _36458.
Proof. exact (EQ_MP (@lem3456848 _89578 _89597 _89598 P x f _36458) (@lem3456847 _89578 _89597 _89598 _36458 x' y t P x f h1)). Qed.
Lemma lem3456850 {_89578 _89597 _89598 : Type'} (_36458 : _89598) (_36459 : _89597) (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term309 _89578 _89597 _89598 P x f _36458 _36459.
Proof. exact (@lem3456849 _89578 _89597 _89598 _36458 x' y t P x f h1 _36459). Qed.
Lemma lem3456851 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (_36458 : _89598) (_36459 : _89597) : (term309 _89578 _89597 _89598 P x f _36458 _36459) = (term69 _89578 _89597 _89598 P x f _36458 _36459).
Proof. exact (eq_refl (term309 _89578 _89597 _89598 P x f _36458 _36459)). Qed.
Lemma lem3456853 {_89578 _89597 _89598 : Type'} (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term310 _89578 _89597 _89598 P f x _36460.
Proof. exact (@lem3456838 _89578 _89597 _89598 P x f x' y h1 _36460). Qed.
Lemma lem3456854 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (x : _89578) (_36460 : _89578 -> Prop) : (term310 _89578 _89597 _89598 P f x _36460) = (term305 _89578 _89597 _89598 P f x _36460).
Proof. exact (eq_refl (term310 _89578 _89597 _89598 P f x _36460)). Qed.
Lemma lem3456855 {_89578 _89597 _89598 : Type'} (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term305 _89578 _89597 _89598 P f x _36460.
Proof. exact (EQ_MP (@lem3456854 _89578 _89597 _89598 P f x _36460) (@lem3456853 _89578 _89597 _89598 _36460 P x f x' y h1)). Qed.
Lemma lem3456856 {_89578 _89597 _89598 : Type'} (_36460 : _89578 -> Prop) (_36461 : _89598) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term311 _89578 _89597 _89598 P f x _36460 _36461.
Proof. exact (@lem3456855 _89578 _89597 _89598 _36460 P x f x' y h1 _36461). Qed.
Lemma lem3456857 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (x : _89578) (_36460 : _89578 -> Prop) : (term311 _89578 _89597 _89598 P f x _36460 _36461) = (term303 _89578 _89597 _89598 P f _36461 x _36460).
Proof. exact (eq_refl (term311 _89578 _89597 _89598 P f x _36460 _36461)). Qed.
Lemma lem3456858 {_89578 _89597 _89598 : Type'} (_36461 : _89598) (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term303 _89578 _89597 _89598 P f _36461 x _36460.
Proof. exact (EQ_MP (@lem3456857 _89578 _89597 _89598 P f _36461 x _36460) (@lem3456856 _89578 _89597 _89598 _36460 _36461 P x f x' y h1)). Qed.
Lemma lem3456859 {_89578 _89597 _89598 : Type'} (_36461 : _89598) (_36460 : _89578 -> Prop) (_36462 : _89597) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term312 _89578 _89597 _89598 P f _36461 x _36460 _36462.
Proof. exact (@lem3456858 _89578 _89597 _89598 _36461 _36460 P x f x' y h1 _36462). Qed.
Lemma lem3456860 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term312 _89578 _89597 _89598 P f _36461 x _36460 _36462) = (term300 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (eq_refl (term312 _89578 _89597 _89598 P f _36461 x _36460 _36462)). Qed.
Lemma lem3456861 {_89578 _89597 _89598 : Type'} (_36461 : _89598) (_36462 : _89597) (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term300 _89578 _89597 _89598 P f _36461 _36462 x _36460.
Proof. exact (EQ_MP (@lem3456860 _89578 _89597 _89598 P f _36461 _36462 x _36460) (@lem3456859 _89578 _89597 _89598 _36461 _36460 _36462 P x f x' y h1)). Qed.
Lemma lem3456869 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : @IN _89578 x t.
Proof. exact (proj2 (@lem3456723 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456873 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : t = (f x' y).
Proof. exact (proj2 (@lem3456725 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456884 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term300 _89578 _89597 _89598 P f _36461 _36462 x _36460) = (term313 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (@lem3453857 (term314 _89597 _89598 P _36461 _36462) (term315 _89578 _89597 _89598 _36460 f _36461 _36462) (term53 _89578 x _36460)). Qed.
Lemma lem3456885 {_89578 _89597 _89598 : Type'} (_36461 : _89598) (_36462 : _89597) (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term313 _89578 _89597 _89598 P f _36461 _36462 x _36460.
Proof. exact (EQ_MP (@lem3456884 _89578 _89597 _89598 P f _36461 _36462 x _36460) (@lem3456861 _89578 _89597 _89598 _36461 _36462 _36460 P x f x' y h1)). Qed.
Lemma lem3456917 {_89578 _89597 _89598 : Type'} (_36458 : _89598) (_36459 : _89597) (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term69 _89578 _89597 _89598 P x f _36458 _36459.
Proof. exact (EQ_MP (@lem3456851 _89578 _89597 _89598 P x f _36458 _36459) (@lem3456850 _89578 _89597 _89598 _36458 _36459 x' y t P x f h1)). Qed.
Lemma lem3456918 {_89578 : Type'} (x : _89578) : (term316 _89578 x) = (term316 _89578 x).
Proof. exact (eq_refl (term316 _89578 x)). Qed.
Lemma lem3456919 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : (term317 _89578 x t) = (term318 _89578 _89597 _89598 x f x' y).
Proof. exact (MK_COMB (@lem3456918 _89578 x) (@lem3456873 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456920 {_89578 _89597 _89598 : Type'} (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term318 _89578 _89597 _89598 x f x' y) = (term70 _89578 _89597 _89598 x f x' y).
Proof. exact (eq_refl (term318 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3456921 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term319 _89578 x t) = (term319 _89578 x t).
Proof. exact (eq_refl (term319 _89578 x t)). Qed.
Lemma lem3456922 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : ((term317 _89578 x t) = (term318 _89578 _89597 _89598 x f x' y)) = ((term317 _89578 x t) = (term70 _89578 _89597 _89598 x f x' y)).
Proof. exact (MK_COMB (@lem3456921 _89578 x t) (@lem3456920 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3456923 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term317 _89578 x t) = (@IN _89578 x t).
Proof. exact (eq_refl (term317 _89578 x t)). Qed.
Lemma lem3456924 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3456925 {_89578 : Type'} (x : _89578) (t : _89578 -> Prop) : (term319 _89578 x t) = (term320 _89578 x t).
Proof. exact (MK_COMB (@lem3456924) (@lem3456923 _89578 x t)). Qed.
Lemma lem3456926 {_89578 _89597 _89598 : Type'} (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term70 _89578 _89597 _89598 x f x' y) = (term70 _89578 _89597 _89598 x f x' y).
Proof. exact (eq_refl (term70 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3456927 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : ((term317 _89578 x t) = (term70 _89578 _89597 _89598 x f x' y)) = ((@IN _89578 x t) = (term70 _89578 _89597 _89598 x f x' y)).
Proof. exact (MK_COMB (@lem3456925 _89578 x t) (@lem3456926 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3456928 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : ((term317 _89578 x t) = (term318 _89578 _89597 _89598 x f x' y)) = ((@IN _89578 x t) = (term70 _89578 _89597 _89598 x f x' y)).
Proof. exact (TRANS (@lem3456922 _89578 _89597 _89598 t x f x' y) (@lem3456927 _89578 _89597 _89598 t x f x' y)). Qed.
Lemma lem3456929 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : (@IN _89578 x t) = (term70 _89578 _89597 _89598 x f x' y).
Proof. exact (EQ_MP (@lem3456928 _89578 _89597 _89598 t x f x' y) (@lem3456919 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456946 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : P x' y.
Proof. exact (proj1 (@lem3456725 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456947 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term321 _89597 _89598 P x' y.
Proof. exact (fun h0 : term314 _89597 _89598 P x' y => @lem3456946 _89578 _89597 _89598 x' y t P x f h1). Qed.
Lemma lem3456949 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3456950 {_89597 _89598 : Type'} (P : type1470 _89597 _89598) (x' : _89598) (y : _89597) : (term321 _89597 _89598 P x' y) = (P x' y).
Proof. exact (@lem3456949 (P x' y)). Qed.
Lemma lem3456951 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : P x' y.
Proof. exact (EQ_MP (@lem3456950 _89597 _89598 P x' y) (@lem3456947 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456953 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term70 _89578 _89597 _89598 x f x' y.
Proof. exact (EQ_MP (@lem3456929 _89578 _89597 _89598 x' y t P x f h1) (@lem3456869 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456954 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term323 _89578 _89597 _89598 x f x' y.
Proof. exact (fun h0 : term324 _89578 _89597 _89598 x f x' y => @lem3456953 _89578 _89597 _89598 x' y t P x f h1). Qed.
Lemma lem3456956 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3456957 {_89578 _89597 _89598 : Type'} (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term323 _89578 _89597 _89598 x f x' y) = (term70 _89578 _89597 _89598 x f x' y).
Proof. exact (@lem3456956 (term70 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3456958 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term70 _89578 _89597 _89598 x f x' y.
Proof. exact (EQ_MP (@lem3456957 _89578 _89597 _89598 x f x' y) (@lem3456954 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456960 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3456961 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (_36458 : _89598) (_36459 : _89597) : (term69 _89578 _89597 _89598 P x f _36458 _36459) = (term68 _89578 _89597 _89598 P x f _36458 _36459).
Proof. exact (@lem3456960 (P _36458 _36459) (term70 _89578 _89597 _89598 x f _36458 _36459)). Qed.
Lemma lem3456963 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3456964 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (_36458 : _89598) (_36459 : _89597) : (term68 _89578 _89597 _89598 P x f _36458 _36459) = (term327 _89578 _89597 _89598 P x f _36458 _36459).
Proof. exact (@lem3456963 (term17 _89578 _89597 _89598 P x f _36458 _36459)). Qed.
Lemma lem3456965 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (_36458 : _89598) (_36459 : _89597) : (term69 _89578 _89597 _89598 P x f _36458 _36459) = (term327 _89578 _89597 _89598 P x f _36458 _36459).
Proof. exact (TRANS (@lem3456961 _89578 _89597 _89598 P x f _36458 _36459) (@lem3456964 _89578 _89597 _89598 P x f _36458 _36459)). Qed.
Lemma lem3456967 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term17 _89578 _89597 _89598 P x f x' y.
Proof. exact (conj (@lem3456951 _89578 _89597 _89598 x' y t P x f h1) (@lem3456958 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456969 {_89578 _89597 _89598 : Type'} (_36458 : _89598) (_36459 : _89597) (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term327 _89578 _89597 _89598 P x f _36458 _36459.
Proof. exact (EQ_MP (@lem3456965 _89578 _89597 _89598 P x f _36458 _36459) (@lem3456917 _89578 _89597 _89598 _36458 _36459 x' y t P x f h1)). Qed.
Lemma lem3456970 {_89578 _89597 _89598 : Type'} (_36458 : _89598) (_36459 : _89597) (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term327 _89578 _89597 _89598 P x f _36458 _36459.
Proof. exact (@lem3456969 _89578 _89597 _89598 _36458 _36459 x' y t P x f h1). Qed.
Lemma lem3456971 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term327 _89578 _89597 _89598 P x f x' y.
Proof. exact (@lem3456970 _89578 _89597 _89598 x' y x' y t P x f h1). Qed.
Lemma lem3456974 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : False.
Proof. exact (@lem3456971 _89578 _89597 _89598 x' y t P x f h1 (@lem3456967 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3456975 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : term328.
Proof. exact (fun h0 : ~ False => @lem3456974 _89578 _89597 _89598 x' y t P x f h1). Qed.
Lemma lem3456977 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3456978 : term328 = False.
Proof. exact (@lem3456977 False). Qed.
Lemma lem3457042 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : P x' y.
Proof. exact (proj1 (@lem3456728 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457043 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term321 _89597 _89598 P x' y.
Proof. exact (fun h0 : term314 _89597 _89598 P x' y => @lem3457042 _89578 _89597 _89598 P x f x' y h1). Qed.
Lemma lem3457045 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3457046 {_89597 _89598 : Type'} (P : type1470 _89597 _89598) (x' : _89598) (y : _89597) : (term321 _89597 _89598 P x' y) = (P x' y).
Proof. exact (@lem3457045 (P x' y)). Qed.
Lemma lem3457047 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : P x' y.
Proof. exact (EQ_MP (@lem3457046 _89597 _89598 P x' y) (@lem3457043 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457049 {_89578 : Type'} (x : _89578 -> Prop) : x = x.
Proof. exact (@lem21386 (_89578 -> Prop) x). Qed.
Lemma lem3457050 {_89578 : Type'} (x : _89578 -> Prop) : x = x.
Proof. exact (@lem3457049 _89578 x). Qed.
Lemma lem3457051 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (f x' y) = (f x' y).
Proof. exact (@lem3457050 _89578 (f x' y)). Qed.
Lemma lem3457052 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : term329 _89578 _89597 _89598 f x' y.
Proof. exact (fun h0 : term330 _89578 _89597 _89598 f x' y => @lem3457051 _89578 _89597 _89598 f x' y). Qed.
Lemma lem3457054 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3457055 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term329 _89578 _89597 _89598 f x' y) = ((f x' y) = (f x' y)).
Proof. exact (@lem3457054 ((f x' y) = (f x' y))). Qed.
Lemma lem3457056 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (f x' y) = (f x' y).
Proof. exact (EQ_MP (@lem3457055 _89578 _89597 _89598 f x' y) (@lem3457052 _89578 _89597 _89598 f x' y)). Qed.
Lemma lem3457058 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term70 _89578 _89597 _89598 x f x' y.
Proof. exact (proj2 (@lem3456728 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457059 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term323 _89578 _89597 _89598 x f x' y.
Proof. exact (fun h0 : term324 _89578 _89597 _89598 x f x' y => @lem3457058 _89578 _89597 _89598 P x f x' y h1). Qed.
Lemma lem3457061 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3457062 {_89578 _89597 _89598 : Type'} (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) : (term323 _89578 _89597 _89598 x f x' y) = (term70 _89578 _89597 _89598 x f x' y).
Proof. exact (@lem3457061 (term70 _89578 _89597 _89598 x f x' y)). Qed.
Lemma lem3457063 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term70 _89578 _89597 _89598 x f x' y.
Proof. exact (EQ_MP (@lem3457062 _89578 _89597 _89598 x f x' y) (@lem3457059 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457065 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3457066 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term331 _89578 _89597 _89598 f _36461 _36462 x _36460) = (term332 _89578 _89597 _89598 f _36461 _36462 x _36460).
Proof. exact (@lem3457065 (_36460 = (f _36461 _36462)) (@IN _89578 x _36460)). Qed.
Lemma lem3457067 {_89597 _89598 : Type'} (P : type1470 _89597 _89598) (_36461 : _89598) (_36462 : _89597) : (term333 _89597 _89598 P _36461 _36462) = (term333 _89597 _89598 P _36461 _36462).
Proof. exact (eq_refl (term333 _89597 _89598 P _36461 _36462)). Qed.
Lemma lem3457068 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term313 _89578 _89597 _89598 P f _36461 _36462 x _36460) = (term334 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (MK_COMB (@lem3457067 _89597 _89598 P _36461 _36462) (@lem3457066 _89578 _89597 _89598 f _36461 _36462 x _36460)). Qed.
Lemma lem3457070 (a : Prop) (b : Prop) : (term325 a b) = (term326 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3457071 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term334 _89578 _89597 _89598 P f _36461 _36462 x _36460) = (term335 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (@lem3457070 (P _36461 _36462) (term336 _89578 _89597 _89598 f _36461 _36462 x _36460)). Qed.
Lemma lem3457072 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term313 _89578 _89597 _89598 P f _36461 _36462 x _36460) = (term335 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (TRANS (@lem3457068 _89578 _89597 _89598 P f _36461 _36462 x _36460) (@lem3457071 _89578 _89597 _89598 P f _36461 _36462 x _36460)). Qed.
Lemma lem3457074 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3457075 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term335 _89578 _89597 _89598 P f _36461 _36462 x _36460) = (term337 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (@lem3457074 (term338 _89578 _89597 _89598 P f _36461 _36462 x _36460)). Qed.
Lemma lem3457076 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (_36461 : _89598) (_36462 : _89597) (x : _89578) (_36460 : _89578 -> Prop) : (term313 _89578 _89597 _89598 P f _36461 _36462 x _36460) = (term337 _89578 _89597 _89598 P f _36461 _36462 x _36460).
Proof. exact (TRANS (@lem3457072 _89578 _89597 _89598 P f _36461 _36462 x _36460) (@lem3457075 _89578 _89597 _89598 P f _36461 _36462 x _36460)). Qed.
Lemma lem3457078 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term339 _89578 _89597 _89598 x f x' y.
Proof. exact (conj (@lem3457056 _89578 _89597 _89598 f x' y) (@lem3457063 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457079 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term340 _89578 _89597 _89598 P x f x' y.
Proof. exact (conj (@lem3457047 _89578 _89597 _89598 P x f x' y h1) (@lem3457078 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457081 {_89578 _89597 _89598 : Type'} (_36461 : _89598) (_36462 : _89597) (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term337 _89578 _89597 _89598 P f _36461 _36462 x _36460.
Proof. exact (EQ_MP (@lem3457076 _89578 _89597 _89598 P f _36461 _36462 x _36460) (@lem3456885 _89578 _89597 _89598 _36461 _36462 _36460 P x f x' y h1)). Qed.
Lemma lem3457082 {_89578 _89597 _89598 : Type'} (_36461 : _89598) (_36462 : _89597) (_36460 : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term337 _89578 _89597 _89598 P f _36461 _36462 x _36460.
Proof. exact (@lem3457081 _89578 _89597 _89598 _36461 _36462 _36460 P x f x' y h1). Qed.
Lemma lem3457083 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term341 _89578 _89597 _89598 P x f x' y.
Proof. exact (@lem3457082 _89578 _89597 _89598 x' y (f x' y) P x f x' y h1). Qed.
Lemma lem3457086 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : False.
Proof. exact (@lem3457083 _89578 _89597 _89598 P x f x' y h1 (@lem3457079 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457087 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : term328.
Proof. exact (fun h0 : ~ False => @lem3457086 _89578 _89597 _89598 P x f x' y h1). Qed.
Lemma lem3457089 (p : Prop) : (term322 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3457090 : term328 = False.
Proof. exact (@lem3457089 False). Qed.
Lemma lem3457091 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term204 _89578 _89597 _89598 P x f x' y) : False.
Proof. exact (EQ_MP (@lem3457090) (@lem3457087 _89578 _89597 _89598 P x f x' y h1)). Qed.
Lemma lem3457092 {_89578 _89597 _89598 : Type'} (x' : _89598) (y : _89597) (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term175 _89578 _89597 _89598 x' y t P x f) : False.
Proof. exact (EQ_MP (@lem3456978) (@lem3456975 _89578 _89597 _89598 x' y t P x f h1)). Qed.
Lemma lem3457093 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term264 _89578 _89597 _89598 t P x f x' y) : False.
Proof. exact (or_elim (@lem3456719 _89578 _89597 _89598 t P x f x' y h1) (fun h0 : term175 _89578 _89597 _89598 x' y t P x f => @lem3457092 _89578 _89597 _89598 x' y t P x f h0) (fun h0 : term204 _89578 _89597 _89598 P x f x' y => @lem3457091 _89578 _89597 _89598 P x f x' y h0)). Qed.
Lemma lem3457094 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term264 _89578 _89597 _89598 t P x f x' y) : (term264 _89578 _89597 _89598 t P x f x' y) = False.
Proof. exact (prop_ext (fun h2 : term264 _89578 _89597 _89598 t P x f x' y => @lem3457093 _89578 _89597 _89598 t P x f x' y h1) (fun h2 : False => @lem3456719 _89578 _89597 _89598 t P x f x' y h1)). Qed.
Lemma lem3457095 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (y : _89597) (h1 : term264 _89578 _89597 _89598 t P x f x' y) : False.
Proof. exact (EQ_MP (@lem3457094 _89578 _89597 _89598 t P x f x' y h1) (@lem3456719 _89578 _89597 _89598 t P x f x' y h1)). Qed.
Lemma lem3457096 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (x' : _89598) (h1 : term267 _89578 _89597 _89598 t P x f x') : False.
Proof. exact (ex_elim (@lem3456599 _89578 _89597 _89598 t P x f x' h1) (fun y : _89597 => fun h0 : term266 _89578 _89597 _89598 t P x f x' y => @lem3457095 _89578 _89597 _89598 t P x f x' y h0)). Qed.
Lemma lem3457097 {_89578 _89597 _89598 : Type'} (t : _89578 -> Prop) (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term269 _89578 _89597 _89598 t P x f) : False.
Proof. exact (ex_elim (@lem3456598 _89578 _89597 _89598 t P x f h1) (fun x' : _89598 => fun h0 : term268 _89578 _89597 _89598 t P x f x' => @lem3457096 _89578 _89597 _89598 t P x f x' h0)). Qed.
Lemma lem3457098 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term34 _89578 _89597 _89598 P x f) : False.
Proof. exact (ex_elim (@lem3456597 _89578 _89597 _89598 P x f h1) (fun t : _89578 -> Prop => fun h0 : term270 _89578 _89597 _89598 P x f t => @lem3457097 _89578 _89597 _89598 t P x f h0)). Qed.
Lemma lem3457099 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term34 _89578 _89597 _89598 P x f) : (term34 _89578 _89597 _89598 P x f) = False.
Proof. exact (prop_ext (fun h2 : term34 _89578 _89597 _89598 P x f => @lem3457098 _89578 _89597 _89598 P x f h1) (fun h2 : False => @lem3455903 _89578 _89597 _89598 P x f h1)). Qed.
Lemma lem3457100 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) (h1 : term34 _89578 _89597 _89598 P x f) : False.
Proof. exact (EQ_MP (@lem3457099 _89578 _89597 _89598 P x f h1) (@lem3455903 _89578 _89597 _89598 P x f h1)). Qed.
Lemma lem3457101 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : term33 _89578 _89597 _89598 P x f.
Proof. exact (fun h0 : term34 _89578 _89597 _89598 P x f => @lem3457100 _89578 _89597 _89598 P x f h0). Qed.
Lemma lem3457102 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (x : _89578) (f : type1517 _89578 _89597 _89598) : (term30 _89578 _89597 _89598 P f x) = (term21 _89578 _89597 _89598 P x f).
Proof. exact (EQ_MP (@lem3455902 _89578 _89597 _89598 P x f) (@lem3457101 _89578 _89597 _89598 P x f)). Qed.
Lemma lem3457107 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term1 _89578 _89597 _89598 P f.
Proof. exact (fun x : _89578 => @lem3457102 _89578 _89597 _89598 P x f). Qed.
Lemma lem3457112 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : term12 _89578 _89597 _89598 f.
Proof. exact (fun P : type1470 _89597 _89598 => @lem3457107 _89578 _89597 _89598 P f). Qed.
Lemma lem3457117 {_89578 _89597 _89598 : Type'} : term16 _89578 _89597 _89598.
Proof. exact (fun f : type1517 _89578 _89597 _89598 => @lem3457112 _89578 _89597 _89598 f). Qed.
Lemma lem3457118 {_89578 _89597 _89598 : Type'} : term15 _89578 _89597 _89598.
Proof. exact (EQ_MP (@lem3455898 _89578 _89597 _89598) (@lem3457117 _89578 _89597 _89598)). Qed.
Lemma lem3457119 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : term342 _89578 _89597 _89598 f.
Proof. exact (@lem3457118 _89578 _89597 _89598 f). Qed.
Lemma lem3457120 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : (term342 _89578 _89597 _89598 f) = (term11 _89578 _89597 _89598 f).
Proof. exact (eq_refl (term342 _89578 _89597 _89598 f)). Qed.
Lemma lem3457121 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) : term11 _89578 _89597 _89598 f.
Proof. exact (EQ_MP (@lem3457120 _89578 _89597 _89598 f) (@lem3457119 _89578 _89597 _89598 f)). Qed.
Lemma lem3457122 {_89578 _89597 _89598 : Type'} (f : type1517 _89578 _89597 _89598) (P : type1470 _89597 _89598) : term343 _89578 _89597 _89598 f P.
Proof. exact (@lem3457121 _89578 _89597 _89598 f P). Qed.
Lemma lem3457123 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : (term343 _89578 _89597 _89598 f P) = (term2 _89578 _89597 _89598 P f).
Proof. exact (eq_refl (term343 _89578 _89597 _89598 f P)). Qed.
Lemma lem3457124 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term2 _89578 _89597 _89598 P f.
Proof. exact (EQ_MP (@lem3457123 _89578 _89597 _89598 P f) (@lem3457122 _89578 _89597 _89598 f P)). Qed.
Lemma lem3457126 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term2 _89578 _89597 _89598 P f.
Proof. exact (@lem3455604 _89578 _89597 _89598 P f (@lem3457124 _89578 _89597 _89598 P f)). Qed.
Lemma lem3457127 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term3 _89578 _89597 _89598 P f) : False.
Proof. exact (@lem3457126 _89578 _89597 _89598 P f (@lem3455588 _89578 _89597 _89598 P f h1)). Qed.
Lemma lem3457128 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term3 _89578 _89597 _89598 P f) : (term3 _89578 _89597 _89598 P f) = False.
Proof. exact (prop_ext (fun h2 : term3 _89578 _89597 _89598 P f => @lem3457127 _89578 _89597 _89598 P f h1) (fun h2 : False => @lem3455588 _89578 _89597 _89598 P f h1)). Qed.
Lemma lem3457129 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) (h1 : term3 _89578 _89597 _89598 P f) : False.
Proof. exact (EQ_MP (@lem3457128 _89578 _89597 _89598 P f h1) (@lem3455588 _89578 _89597 _89598 P f h1)). Qed.
Lemma lem3457130 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term2 _89578 _89597 _89598 P f.
Proof. exact (fun h0 : term3 _89578 _89597 _89598 P f => @lem3457129 _89578 _89597 _89598 P f h0). Qed.
Lemma lem3457131 {_89578 _89597 _89598 : Type'} (P : type1470 _89597 _89598) (f : type1517 _89578 _89597 _89598) : term1 _89578 _89597 _89598 P f.
Proof. exact (EQ_MP (@lem3455587 _89578 _89597 _89598 P f) (@lem3457130 _89578 _89597 _89598 P f)). Qed.
