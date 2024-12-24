Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATO_CLAUSES_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import ITERATO_CLAUSES_GEN_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19490_spec.
Require Import thm19792_spec.
Require Import thm20230_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem6774672 {A K : Type'} (dom : A -> Prop) : term0 A K dom.
Proof. exact (@lem6774661 A K dom). Qed.
Lemma lem6774673 {A K : Type'} (dom : A -> Prop) : (term0 A K dom) = (term1 A K dom).
Proof. exact (eq_refl (term0 A K dom)). Qed.
Lemma lem6774674 {A K : Type'} (dom : A -> Prop) : term1 A K dom.
Proof. exact (EQ_MP (@lem6774673 A K dom) (@lem6774672 A K dom)). Qed.
Lemma lem6774675 {A K : Type'} (dom : A -> Prop) (neut : A) : term2 A K dom neut.
Proof. exact (@lem6774674 A K dom neut). Qed.
Lemma lem6774676 {A K : Type'} (dom : A -> Prop) (neut : A) : (term2 A K dom neut) = (term3 A K dom neut).
Proof. exact (eq_refl (term2 A K dom neut)). Qed.
Lemma lem6774677 {A K : Type'} (dom : A -> Prop) (neut : A) : term3 A K dom neut.
Proof. exact (EQ_MP (@lem6774676 A K dom neut) (@lem6774675 A K dom neut)). Qed.
Lemma lem6774678 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term4 A K dom neut op.
Proof. exact (@lem6774677 A K dom neut op). Qed.
Lemma lem6774679 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term4 A K dom neut op) = (term5 A K dom neut op).
Proof. exact (eq_refl (term4 A K dom neut op)). Qed.
Lemma lem6774680 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term5 A K dom neut op.
Proof. exact (EQ_MP (@lem6774679 A K dom neut op) (@lem6774678 A K dom neut op)). Qed.
Lemma lem6774681 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term6 A K dom neut op ltle.
Proof. exact (@lem6774680 A K dom neut op ltle). Qed.
Lemma lem6774682 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term6 A K dom neut op ltle) = (term7 A K dom neut op ltle).
Proof. exact (eq_refl (term6 A K dom neut op ltle)). Qed.
Lemma lem6774683 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term7 A K dom neut op ltle.
Proof. exact (EQ_MP (@lem6774682 A K dom neut op ltle) (@lem6774681 A K dom neut op ltle)). Qed.
Lemma lem6774684 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term8 A K dom neut op ltle f.
Proof. exact (@lem6774683 A K dom neut op ltle f). Qed.
Lemma lem6774685 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term8 A K dom neut op ltle f) = (term9 A K dom neut op ltle f).
Proof. exact (eq_refl (term8 A K dom neut op ltle f)). Qed.
Lemma lem6774686 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term9 A K dom neut op ltle f.
Proof. exact (EQ_MP (@lem6774685 A K dom neut op ltle f) (@lem6774684 A K dom neut op ltle f)). Qed.
Lemma lem6774687 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term10 A K dom neut op ltle f.
Proof. exact (proj2 (@lem6774686 A K dom neut op ltle f)). Qed.
Lemma lem6774688 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term10 A K dom neut op ltle f.
Proof. exact (h1). Qed.
Lemma lem6774689 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term11 A K dom neut op ltle f i.
Proof. exact (@lem6774688 A K dom neut op ltle f h1 i). Qed.
Lemma lem6774690 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term11 A K dom neut op ltle f i) = (term12 A K i dom neut op ltle f).
Proof. exact (eq_refl (term11 A K dom neut op ltle f i)). Qed.
Lemma lem6774691 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term12 A K i dom neut op ltle f.
Proof. exact (EQ_MP (@lem6774690 A K i dom neut op ltle f) (@lem6774689 A K i dom neut op ltle f h1)). Qed.
Lemma lem6774692 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term13 A K i dom neut op ltle f k.
Proof. exact (@lem6774691 A K i dom neut op ltle f h1 k). Qed.
Lemma lem6774693 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term13 A K i dom neut op ltle f k) = (term14 A K i dom neut op ltle k f).
Proof. exact (eq_refl (term13 A K i dom neut op ltle f k)). Qed.
Lemma lem6774694 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term14 A K i dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6774693 A K i dom neut op ltle k f) (@lem6774692 A K i k dom neut op ltle f h1)). Qed.
Lemma lem6774695 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term15 A K ltle k f dom neut i) : term15 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6774696 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term10 A K dom neut op ltle f) (h2 : term15 A K ltle k f dom neut i) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (@lem6774694 A K i k dom neut op ltle f h1 (@lem6774695 A K ltle k f dom neut i h2)). Qed.
Lemma lem6774697 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term15 A K ltle k f dom neut i) : term18 A K i dom neut op ltle k f.
Proof. exact (fun h0 : term10 A K dom neut op ltle f => @lem6774696 A K op ltle k f dom neut i h0 h1). Qed.
Lemma lem6774698 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term10 A K dom neut op ltle f.
Proof. exact (h1). Qed.
Lemma lem6774699 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term10 A K dom neut op ltle f) (h2 : term15 A K ltle k f dom neut i) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (@lem6774697 A K op ltle k f dom neut i h2 (@lem6774698 A K dom neut op ltle f h1)). Qed.
Lemma lem6774700 {A K : Type'} (i : K) (k : K -> Prop) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term14 A K i dom neut op ltle k f.
Proof. exact (fun h0 : term15 A K ltle k f dom neut i => @lem6774699 A K op ltle k f dom neut i h1 h0). Qed.
Lemma lem6774701 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term12 A K i dom neut op ltle f.
Proof. exact (fun k : K -> Prop => @lem6774700 A K i k dom neut op ltle f h1). Qed.
Lemma lem6774702 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (h1 : term10 A K dom neut op ltle f) : term10 A K dom neut op ltle f.
Proof. exact (fun i : K => @lem6774701 A K i dom neut op ltle f h1). Qed.
Lemma lem6774703 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term19 A K dom neut op ltle f.
Proof. exact (fun h0 : term10 A K dom neut op ltle f => @lem6774702 A K dom neut op ltle f h0). Qed.
Lemma lem6774704 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term10 A K dom neut op ltle f.
Proof. exact (@lem6774703 A K dom neut op ltle f (@lem6774687 A K dom neut op ltle f)). Qed.
Lemma lem6774705 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (i : K) : term11 A K dom neut op ltle f i.
Proof. exact (@lem6774704 A K dom neut op ltle f i). Qed.
Lemma lem6774706 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term11 A K dom neut op ltle f i) = (term12 A K i dom neut op ltle f).
Proof. exact (eq_refl (term11 A K dom neut op ltle f i)). Qed.
Lemma lem6774707 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term12 A K i dom neut op ltle f.
Proof. exact (EQ_MP (@lem6774706 A K i dom neut op ltle f) (@lem6774705 A K dom neut op ltle f i)). Qed.
Lemma lem6774708 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (k : K -> Prop) : term13 A K i dom neut op ltle f k.
Proof. exact (@lem6774707 A K i dom neut op ltle f k). Qed.
Lemma lem6774709 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : (term13 A K i dom neut op ltle f k) = (term14 A K i dom neut op ltle k f).
Proof. exact (eq_refl (term13 A K i dom neut op ltle f k)). Qed.
Lemma lem6774711 {A K : Type'} (dom : A -> Prop) : term0 A K dom.
Proof. exact (@lem6774661 A K dom). Qed.
Lemma lem6774712 {A K : Type'} (dom : A -> Prop) : (term0 A K dom) = (term1 A K dom).
Proof. exact (eq_refl (term0 A K dom)). Qed.
Lemma lem6774713 {A K : Type'} (dom : A -> Prop) : term1 A K dom.
Proof. exact (EQ_MP (@lem6774712 A K dom) (@lem6774711 A K dom)). Qed.
Lemma lem6774714 {A K : Type'} (dom : A -> Prop) (neut : A) : term2 A K dom neut.
Proof. exact (@lem6774713 A K dom neut). Qed.
Lemma lem6774715 {A K : Type'} (dom : A -> Prop) (neut : A) : (term2 A K dom neut) = (term3 A K dom neut).
Proof. exact (eq_refl (term2 A K dom neut)). Qed.
Lemma lem6774716 {A K : Type'} (dom : A -> Prop) (neut : A) : term3 A K dom neut.
Proof. exact (EQ_MP (@lem6774715 A K dom neut) (@lem6774714 A K dom neut)). Qed.
Lemma lem6774717 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term4 A K dom neut op.
Proof. exact (@lem6774716 A K dom neut op). Qed.
Lemma lem6774718 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : (term4 A K dom neut op) = (term5 A K dom neut op).
Proof. exact (eq_refl (term4 A K dom neut op)). Qed.
Lemma lem6774719 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term5 A K dom neut op.
Proof. exact (EQ_MP (@lem6774718 A K dom neut op) (@lem6774717 A K dom neut op)). Qed.
Lemma lem6774720 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term6 A K dom neut op ltle.
Proof. exact (@lem6774719 A K dom neut op ltle). Qed.
Lemma lem6774721 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : (term6 A K dom neut op ltle) = (term7 A K dom neut op ltle).
Proof. exact (eq_refl (term6 A K dom neut op ltle)). Qed.
Lemma lem6774722 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term7 A K dom neut op ltle.
Proof. exact (EQ_MP (@lem6774721 A K dom neut op ltle) (@lem6774720 A K dom neut op ltle)). Qed.
Lemma lem6774723 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term8 A K dom neut op ltle f.
Proof. exact (@lem6774722 A K dom neut op ltle f). Qed.
Lemma lem6774724 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : (term8 A K dom neut op ltle f) = (term9 A K dom neut op ltle f).
Proof. exact (eq_refl (term8 A K dom neut op ltle f)). Qed.
Lemma lem6774725 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term9 A K dom neut op ltle f.
Proof. exact (EQ_MP (@lem6774724 A K dom neut op ltle f) (@lem6774723 A K dom neut op ltle f)). Qed.
Lemma lem6774736 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term20 A K f dom neut k ltle i) : term20 A K f dom neut k ltle i.
Proof. exact (h1). Qed.
Lemma lem6774737 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term21 K k ltle i.
Proof. exact (h1). Qed.
Lemma lem6774738 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term22 A K k f dom neut) : term22 A K k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6774742 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (proj1 (@lem6774725 A K dom neut op ltle f)). Qed.
Lemma lem6774743 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (@lem6774742 A K dom op ltle f neut). Qed.
Lemma lem6774744 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem6774745 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (term23 A K dom neut op ltle f) = (@eq A neut).
Proof. exact (MK_COMB (@lem6774744 A) (@lem6774743 A K dom op ltle f neut)). Qed.
Lemma lem6774746 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6774747 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut) = (neut = neut).
Proof. exact (MK_COMB (@lem6774745 A K dom op ltle f neut) (@lem6774746 A neut)). Qed.
Lemma lem6774749 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem6774750 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem6774749 A x). Qed.
Lemma lem6774751 {A : Type'} (neut : A) : (neut = neut) = True.
Proof. exact (@lem6774750 A neut). Qed.
Lemma lem6774752 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut) = True.
Proof. exact (TRANS (@lem6774747 A K dom op ltle f neut) (@lem6774751 A neut)). Qed.
Lemma lem6774753 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : True = ((@iterato A K dom neut op ltle (@EMPTY K) f) = neut).
Proof. exact (SYM (@lem6774752 A K dom op ltle f neut)). Qed.
Lemma lem6774754 {A K : Type'} (dom : A -> Prop) (op : type1400 A) (ltle : type1402 K) (f : K -> A) (neut : A) : (@iterato A K dom neut op ltle (@EMPTY K) f) = neut.
Proof. exact (EQ_MP (@lem6774753 A K dom op ltle f neut) (@lem0)). Qed.
Lemma lem6774766 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term14 A K i dom neut op ltle k f.
Proof. exact (EQ_MP (@lem6774709 A K i dom neut op ltle k f) (@lem6774708 A K i dom neut op ltle f k)). Qed.
Lemma lem6774767 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term14 A K i dom neut op ltle k f.
Proof. exact (@lem6774766 A K i dom neut op ltle k f). Qed.
Lemma lem6774769 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6774770 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term15 A K ltle k f dom neut i) = (term25 A K ltle k f dom neut i).
Proof. exact (@lem6774769 (term15 A K ltle k f dom neut i)). Qed.
Lemma lem6774771 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term25 A K ltle k f dom neut i) = (term15 A K ltle k f dom neut i).
Proof. exact (SYM (@lem6774770 A K ltle k f dom neut i)). Qed.
Lemma lem6774772 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term26 A K ltle k f dom neut i) : term26 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6774775 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term27 A K ltle k f dom neut i) : term27 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6774776 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term28 A K ltle k f dom neut i.
Proof. exact (fun h0 : term27 A K ltle k f dom neut i => @lem6774775 A K ltle k f dom neut i h0). Qed.
Lemma lem6774777 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term28 A K ltle k f dom neut i) : term28 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6774778 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term27 A K ltle k f dom neut i) : term27 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6774779 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term27 A K ltle k f dom neut i) (h2 : term28 A K ltle k f dom neut i) : term27 A K ltle k f dom neut i.
Proof. exact (@lem6774777 A K ltle k f dom neut i h2 (@lem6774778 A K ltle k f dom neut i h1)). Qed.
Lemma lem6774780 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term27 A K ltle k f dom neut i) : term29 A K ltle k f dom neut i.
Proof. exact (fun h0 : term28 A K ltle k f dom neut i => @lem6774779 A K ltle k f dom neut i h1 h0). Qed.
Lemma lem6774781 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term28 A K ltle k f dom neut i) : term28 A K ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6774782 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term27 A K ltle k f dom neut i) (h2 : term28 A K ltle k f dom neut i) : term27 A K ltle k f dom neut i.
Proof. exact (@lem6774780 A K ltle k f dom neut i h1 (@lem6774781 A K ltle k f dom neut i h2)). Qed.
Lemma lem6774783 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term28 A K ltle k f dom neut i) : term28 A K ltle k f dom neut i.
Proof. exact (fun h0 : term27 A K ltle k f dom neut i => @lem6774782 A K ltle k f dom neut i h0 h1). Qed.
Lemma lem6774784 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term30 A K ltle k f dom neut i.
Proof. exact (fun h0 : term28 A K ltle k f dom neut i => @lem6774783 A K ltle k f dom neut i h0). Qed.
Lemma lem6774787 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term28 A K ltle k f dom neut i.
Proof. exact (@lem6774784 A K ltle k f dom neut i (@lem6774776 A K ltle k f dom neut i)). Qed.
Lemma lem6774788 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term28 A K ltle k f dom neut i.
Proof. exact (@lem6774787 A K ltle k f dom neut i). Qed.
Lemma lem6774832 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem6774833 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term25 A K ltle k f dom neut i) = (term31 A K ltle k f dom neut i).
Proof. exact (@lem6774832 (term26 A K ltle k f dom neut i)). Qed.
Lemma lem6774835 (t : Prop) : (term32 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6774836 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term31 A K ltle k f dom neut i) = (term15 A K ltle k f dom neut i).
Proof. exact (@lem6774835 (term15 A K ltle k f dom neut i)). Qed.
Lemma lem6774839 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term25 A K ltle k f dom neut i) = (term15 A K ltle k f dom neut i).
Proof. exact (TRANS (@lem6774833 A K ltle k f dom neut i) (@lem6774836 A K ltle k f dom neut i)). Qed.
Lemma lem6774868 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term33 K k ltle i) = (term33 K k ltle i).
Proof. exact (eq_refl (term33 K k ltle i)). Qed.
Lemma lem6774869 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term34 A K ltle k f dom neut i) = (term35 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6774868 K k ltle i) (@lem6774839 A K ltle k f dom neut i)). Qed.
Lemma lem6774872 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term36 A K k f dom neut) = (term36 A K k f dom neut).
Proof. exact (eq_refl (term36 A K k f dom neut)). Qed.
Lemma lem6774873 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term27 A K ltle k f dom neut i) = (term37 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6774872 A K k f dom neut) (@lem6774869 A K ltle k f dom neut i)). Qed.
Lemma lem6774876 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term38 A K k f dom neut i) = (term39 A K k f dom neut i).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6774873 A K ltle k f dom neut i)). Qed.
Lemma lem6774877 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6774878 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term40 A K k f dom neut i) = (term41 A K k f dom neut i).
Proof. exact (MK_COMB (@lem6774877 K) (@lem6774876 A K k f dom neut i)). Qed.
Lemma lem6774883 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term42 A K f dom neut i) = (term43 A K f dom neut i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6774878 A K k f dom neut i)). Qed.
Lemma lem6774884 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6774885 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term44 A K f dom neut i) = (term45 A K f dom neut i).
Proof. exact (MK_COMB (@lem6774884 K) (@lem6774883 A K f dom neut i)). Qed.
Lemma lem6774890 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) : (term46 A K dom neut i) = (term47 A K dom neut i).
Proof. exact (fun_ext (fun f : K -> A => @lem6774885 A K f dom neut i)). Qed.
Lemma lem6774891 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6774892 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) : (term48 A K dom neut i) = (term49 A K dom neut i).
Proof. exact (MK_COMB (@lem6774891 A K) (@lem6774890 A K dom neut i)). Qed.
Lemma lem6774897 {A K : Type'} (neut : A) (i : K) : (term50 A K neut i) = (term51 A K neut i).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6774892 A K dom neut i)). Qed.
Lemma lem6774898 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6774899 {A K : Type'} (neut : A) (i : K) : (term52 A K neut i) = (term53 A K neut i).
Proof. exact (MK_COMB (@lem6774898 A) (@lem6774897 A K neut i)). Qed.
Lemma lem6774904 {A K : Type'} (i : K) : (term54 A K i) = (term55 A K i).
Proof. exact (fun_ext (fun neut : A => @lem6774899 A K neut i)). Qed.
Lemma lem6774905 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6774906 {A K : Type'} (i : K) : (term56 A K i) = (term57 A K i).
Proof. exact (MK_COMB (@lem6774905 A) (@lem6774904 A K i)). Qed.
Lemma lem6774911 {A K : Type'} : (term58 A K) = (term59 A K).
Proof. exact (fun_ext (fun i : K => @lem6774906 A K i)). Qed.
Lemma lem6774912 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6774919 {A K : Type'} : (term60 A K) = (term61 A K).
Proof. exact (MK_COMB (@lem6774912 K) (@lem6774911 A K)). Qed.
Lemma lem6774920 {A K : Type'} (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : _88612 = (term62 A K).
Proof. exact (h1). Qed.
Lemma lem6774921 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6774922 {A K : Type'} (k : K -> Prop) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k) = (term63 A K k).
Proof. exact (MK_COMB (@lem6774920 A K _88612 h1) (@lem6774921 K k)). Qed.
Lemma lem6774923 {A K : Type'} (k : K -> Prop) : (term63 A K k) = (term64 A K k).
Proof. exact (eq_refl (term63 A K k)). Qed.
Lemma lem6774924 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term65 A K _88612 k) = (term65 A K _88612 k).
Proof. exact (eq_refl (term65 A K _88612 k)). Qed.
Lemma lem6774925 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((_88612 k) = (term63 A K k)) = ((_88612 k) = (term64 A K k)).
Proof. exact (MK_COMB (@lem6774924 A K _88612 k) (@lem6774923 A K k)). Qed.
Lemma lem6774926 {A K : Type'} (k : K -> Prop) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k) = (term64 A K k).
Proof. exact (EQ_MP (@lem6774925 A K _88612 k) (@lem6774922 A K k _88612 h1)). Qed.
Lemma lem6774927 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6774928 {A K : Type'} (k : K -> Prop) (f : K -> A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k f) = (term66 A K k f).
Proof. exact (MK_COMB (@lem6774926 A K k _88612 h1) (@lem6774927 A K f)). Qed.
Lemma lem6774929 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term66 A K k f) = (term67 A K k f).
Proof. exact (eq_refl (term66 A K k f)). Qed.
Lemma lem6774930 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term68 A K _88612 k f) = (term68 A K _88612 k f).
Proof. exact (eq_refl (term68 A K _88612 k f)). Qed.
Lemma lem6774931 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((_88612 k f) = (term66 A K k f)) = ((_88612 k f) = (term67 A K k f)).
Proof. exact (MK_COMB (@lem6774930 A K _88612 k f) (@lem6774929 A K k f)). Qed.
Lemma lem6774932 {A K : Type'} (k : K -> Prop) (f : K -> A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k f) = (term67 A K k f).
Proof. exact (EQ_MP (@lem6774931 A K _88612 k f) (@lem6774928 A K k f _88612 h1)). Qed.
Lemma lem6774933 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6774934 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k f dom) = (term69 A K k f dom).
Proof. exact (MK_COMB (@lem6774932 A K k f _88612 h1) (@lem6774933 A dom)). Qed.
Lemma lem6774935 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term69 A K k f dom) = (term70 A K k f dom).
Proof. exact (eq_refl (term69 A K k f dom)). Qed.
Lemma lem6774936 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term71 A K _88612 k f dom) = (term71 A K _88612 k f dom).
Proof. exact (eq_refl (term71 A K _88612 k f dom)). Qed.
Lemma lem6774937 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((_88612 k f dom) = (term69 A K k f dom)) = ((_88612 k f dom) = (term70 A K k f dom)).
Proof. exact (MK_COMB (@lem6774936 A K _88612 k f dom) (@lem6774935 A K k f dom)). Qed.
Lemma lem6774938 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k f dom) = (term70 A K k f dom).
Proof. exact (EQ_MP (@lem6774937 A K _88612 k f dom) (@lem6774934 A K k f dom _88612 h1)). Qed.
Lemma lem6774939 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6774940 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k f dom neut) = (term72 A K k f dom neut).
Proof. exact (MK_COMB (@lem6774938 A K k f dom _88612 h1) (@lem6774939 A neut)). Qed.
Lemma lem6774941 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term72 A K k f dom neut) = (term73 A K k f dom neut).
Proof. exact (eq_refl (term72 A K k f dom neut)). Qed.
Lemma lem6774942 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term74 A K _88612 k f dom neut) = (term74 A K _88612 k f dom neut).
Proof. exact (eq_refl (term74 A K _88612 k f dom neut)). Qed.
Lemma lem6774943 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut) = (term72 A K k f dom neut)) = ((_88612 k f dom neut) = (term73 A K k f dom neut)).
Proof. exact (MK_COMB (@lem6774942 A K _88612 k f dom neut) (@lem6774941 A K k f dom neut)). Qed.
Lemma lem6774944 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (_88612 k f dom neut) = (term73 A K k f dom neut).
Proof. exact (EQ_MP (@lem6774943 A K _88612 k f dom neut) (@lem6774940 A K k f dom neut _88612 h1)). Qed.
Lemma lem6774984 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term75 A K ltle k f dom neut j i) = (term75 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term75 A K ltle k f dom neut j i)). Qed.
Lemma lem6774985 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term76 A K ltle k f dom neut i) = (term76 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6774984 A K ltle k f dom neut j i)). Qed.
Lemma lem6774986 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6774987 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term77 A K ltle k f dom neut i) = (term77 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6774986 K) (@lem6774985 A K ltle k f dom neut i)). Qed.
Lemma lem6775016 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term78 K k ltle j i) = (term78 K k ltle j i).
Proof. exact (eq_refl (term78 K k ltle j i)). Qed.
Lemma lem6775017 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term79 K k ltle i) = (term79 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6775016 K k ltle j i)). Qed.
Lemma lem6775018 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775019 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term80 K k ltle i) = (term80 K k ltle i).
Proof. exact (MK_COMB (@lem6775018 K) (@lem6775017 K k ltle i)). Qed.
Lemma lem6775020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775021 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term81 K k ltle i) = (term81 K k ltle i).
Proof. exact (MK_COMB (@lem6775020) (@lem6775019 K k ltle i)). Qed.
Lemma lem6775022 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term82 A K ltle k f dom neut i) = (term82 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775021 K k ltle i) (@lem6774987 A K ltle k f dom neut i)). Qed.
Lemma lem6775024 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term73 A K k f dom neut) = (_88612 k f dom neut).
Proof. exact (SYM (@lem6774944 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775025 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term73 A K k f dom neut) = (_88612 k f dom neut).
Proof. exact (@lem6775024 A K k f dom neut _88612 h1). Qed.
Lemma lem6775026 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6775027 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term83 A K k f dom neut) = (term84 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775026 K) (@lem6775025 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775028 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6775029 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term22 A K k f dom neut) = (term85 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775028 K) (@lem6775027 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775031 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term86 A K k f dom neut) = (term87 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775030) (@lem6775029 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775032 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term15 A K ltle k f dom neut i) = (term88 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775031 A K k f dom neut _88612 h1) (@lem6775022 A K ltle k f dom neut i)). Qed.
Lemma lem6775055 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term89 K k ltle j i) = (term89 K k ltle j i).
Proof. exact (eq_refl (term89 K k ltle j i)). Qed.
Lemma lem6775056 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term90 K k ltle i) = (term90 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6775055 K k ltle j i)). Qed.
Lemma lem6775057 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775058 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term21 K k ltle i) = (term21 K k ltle i).
Proof. exact (MK_COMB (@lem6775057 K) (@lem6775056 K k ltle i)). Qed.
Lemma lem6775059 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6775060 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term33 K k ltle i) = (term33 K k ltle i).
Proof. exact (MK_COMB (@lem6775059) (@lem6775058 K k ltle i)). Qed.
Lemma lem6775061 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term35 A K ltle k f dom neut i) = (term91 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775060 K k ltle i) (@lem6775032 A K ltle k f dom neut i _88612 h1)). Qed.
Lemma lem6775063 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term73 A K k f dom neut) = (_88612 k f dom neut).
Proof. exact (SYM (@lem6774944 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775064 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term73 A K k f dom neut) = (_88612 k f dom neut).
Proof. exact (@lem6775063 A K k f dom neut _88612 h1). Qed.
Lemma lem6775065 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6775066 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term83 A K k f dom neut) = (term84 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775065 K) (@lem6775064 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775067 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6775068 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term22 A K k f dom neut) = (term85 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775067 K) (@lem6775066 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6775070 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term36 A K k f dom neut) = (term92 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775069) (@lem6775068 A K k f dom neut _88612 h1)). Qed.
Lemma lem6775071 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term37 A K ltle k f dom neut i) = (term93 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775070 A K k f dom neut _88612 h1) (@lem6775061 A K ltle k f dom neut i _88612 h1)). Qed.
Lemma lem6775072 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term39 A K k f dom neut i) = (term94 A K _88612 k f dom neut i).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6775071 A K ltle k f dom neut i _88612 h1)). Qed.
Lemma lem6775073 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6775074 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term41 A K k f dom neut i) = (term95 A K _88612 k f dom neut i).
Proof. exact (MK_COMB (@lem6775073 K) (@lem6775072 A K k f dom neut i _88612 h1)). Qed.
Lemma lem6775075 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term43 A K f dom neut i) = (term96 A K _88612 f dom neut i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775074 A K k f dom neut i _88612 h1)). Qed.
Lemma lem6775076 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6775077 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term45 A K f dom neut i) = (term97 A K _88612 f dom neut i).
Proof. exact (MK_COMB (@lem6775076 K) (@lem6775075 A K f dom neut i _88612 h1)). Qed.
Lemma lem6775078 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term47 A K dom neut i) = (term98 A K _88612 dom neut i).
Proof. exact (fun_ext (fun f : K -> A => @lem6775077 A K f dom neut i _88612 h1)). Qed.
Lemma lem6775079 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775080 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term49 A K dom neut i) = (term99 A K _88612 dom neut i).
Proof. exact (MK_COMB (@lem6775079 A K) (@lem6775078 A K dom neut i _88612 h1)). Qed.
Lemma lem6775081 {A K : Type'} (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term51 A K neut i) = (term100 A K _88612 neut i).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775080 A K dom neut i _88612 h1)). Qed.
Lemma lem6775082 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775083 {A K : Type'} (neut : A) (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term53 A K neut i) = (term101 A K _88612 neut i).
Proof. exact (MK_COMB (@lem6775082 A) (@lem6775081 A K neut i _88612 h1)). Qed.
Lemma lem6775084 {A K : Type'} (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term55 A K i) = (term102 A K _88612 i).
Proof. exact (fun_ext (fun neut : A => @lem6775083 A K neut i _88612 h1)). Qed.
Lemma lem6775085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775086 {A K : Type'} (i : K) (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term57 A K i) = (term103 A K _88612 i).
Proof. exact (MK_COMB (@lem6775085 A) (@lem6775084 A K i _88612 h1)). Qed.
Lemma lem6775087 {A K : Type'} (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term59 A K) = (term104 A K _88612).
Proof. exact (fun_ext (fun i : K => @lem6775086 A K i _88612 h1)). Qed.
Lemma lem6775088 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775089 {A K : Type'} (_88612 : type849 A K) (h1 : _88612 = (term62 A K)) : (term61 A K) = (term105 A K _88612).
Proof. exact (MK_COMB (@lem6775088 K) (@lem6775087 A K _88612 h1)). Qed.
Lemma lem6775090 {A K : Type'} (_88612 : type849 A K) : term106 A K _88612.
Proof. exact (fun h0 : _88612 = (term62 A K) => @lem6775089 A K _88612 h0). Qed.
Lemma lem6775091 {A K : Type'} : term107 A K.
Proof. exact (fun _88612 : type849 A K => @lem6775090 A K _88612). Qed.
Lemma lem6775093 {_3603 : Type'} (P : Prop) (c : _3603) (Q : _3603 -> Prop) : term108 _3603 P c Q.
Proof. exact (EQ_MP (@lem20230 _3603 P c Q) (@lem0)). Qed.
Lemma lem6775094 {A K : Type'} (P : Prop) (c : type849 A K) (Q : type219 A K) : term109 A K P c Q.
Proof. exact (@lem6775093 (type849 A K) P c Q). Qed.
Lemma lem6775095 {A K : Type'} : term110 A K.
Proof. exact (@lem6775094 A K (term61 A K) (term62 A K) (term111 A K)). Qed.
Lemma lem6775096 {A K : Type'} (_88612 : type849 A K) : (term112 A K _88612) = (term105 A K _88612).
Proof. exact (eq_refl (term112 A K _88612)). Qed.
Lemma lem6775097 {A K : Type'} : (term113 A K) = (term113 A K).
Proof. exact (eq_refl (term113 A K)). Qed.
Lemma lem6775098 {A K : Type'} (_88612 : type849 A K) : ((term61 A K) = (term112 A K _88612)) = ((term61 A K) = (term105 A K _88612)).
Proof. exact (MK_COMB (@lem6775097 A K) (@lem6775096 A K _88612)). Qed.
Lemma lem6775099 {A K : Type'} (_88612 : type849 A K) : (term114 A K _88612) = (term114 A K _88612).
Proof. exact (eq_refl (term114 A K _88612)). Qed.
Lemma lem6775100 {A K : Type'} (_88612 : type849 A K) : (term115 A K _88612) = (term106 A K _88612).
Proof. exact (MK_COMB (@lem6775099 A K _88612) (@lem6775098 A K _88612)). Qed.
Lemma lem6775101 {A K : Type'} : (term116 A K) = (term117 A K).
Proof. exact (fun_ext (fun _88612 : type849 A K => @lem6775100 A K _88612)). Qed.
Lemma lem6775102 {A K : Type'} : (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop))). Qed.
Lemma lem6775103 {A K : Type'} : (term118 A K) = (term107 A K).
Proof. exact (MK_COMB (@lem6775102 A K) (@lem6775101 A K)). Qed.
Lemma lem6775104 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6775105 {A K : Type'} : (term119 A K) = (term120 A K).
Proof. exact (MK_COMB (@lem6775104) (@lem6775103 A K)). Qed.
Lemma lem6775106 {A K : Type'} (_88612 : type849 A K) : (term112 A K _88612) = (term105 A K _88612).
Proof. exact (eq_refl (term112 A K _88612)). Qed.
Lemma lem6775107 {A K : Type'} (_88612 : type849 A K) : (term114 A K _88612) = (term114 A K _88612).
Proof. exact (eq_refl (term114 A K _88612)). Qed.
Lemma lem6775108 {A K : Type'} (_88612 : type849 A K) : (term121 A K _88612) = (term122 A K _88612).
Proof. exact (MK_COMB (@lem6775107 A K _88612) (@lem6775106 A K _88612)). Qed.
Lemma lem6775109 {A K : Type'} : (term123 A K) = (term124 A K).
Proof. exact (fun_ext (fun _88612 : type849 A K => @lem6775108 A K _88612)). Qed.
Lemma lem6775110 {A K : Type'} : (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop))). Qed.
Lemma lem6775111 {A K : Type'} : (term125 A K) = (term126 A K).
Proof. exact (MK_COMB (@lem6775110 A K) (@lem6775109 A K)). Qed.
Lemma lem6775112 {A K : Type'} : (term113 A K) = (term113 A K).
Proof. exact (eq_refl (term113 A K)). Qed.
Lemma lem6775113 {A K : Type'} : ((term61 A K) = (term125 A K)) = ((term61 A K) = (term126 A K)).
Proof. exact (MK_COMB (@lem6775112 A K) (@lem6775111 A K)). Qed.
Lemma lem6775114 {A K : Type'} : (term110 A K) = (term127 A K).
Proof. exact (MK_COMB (@lem6775105 A K) (@lem6775113 A K)). Qed.
Lemma lem6775115 {A K : Type'} : term127 A K.
Proof. exact (EQ_MP (@lem6775114 A K) (@lem6775095 A K)). Qed.
Lemma lem6775116 {A K : Type'} : (term61 A K) = (term126 A K).
Proof. exact (@lem6775115 A K (@lem6775091 A K)). Qed.
Lemma lem6775118 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term128 _3571 _3575 t)) = (term129 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6775119 {A K : Type'} (s : type849 A K) (t : type849 A K) : (s = (term130 A K t)) = (term131 A K s t).
Proof. exact (@lem6775118 (type781 A K) (K -> Prop) s t). Qed.
Lemma lem6775120 {A K : Type'} (_88612 : type849 A K) : (_88612 = (term132 A K)) = (term133 A K _88612).
Proof. exact (@lem6775119 A K _88612 (term62 A K)). Qed.
Lemma lem6775121 {A K : Type'} (k : K -> Prop) : (term63 A K k) = (term64 A K k).
Proof. exact (eq_refl (term63 A K k)). Qed.
Lemma lem6775122 {A K : Type'} : (term132 A K) = (term62 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775121 A K k)). Qed.
Lemma lem6775123 {A K : Type'} (_88612 : type849 A K) : (@eq ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612) = (@eq ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612).
Proof. exact (eq_refl (@eq ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612)). Qed.
Lemma lem6775124 {A K : Type'} (_88612 : type849 A K) : (_88612 = (term132 A K)) = (_88612 = (term62 A K)).
Proof. exact (MK_COMB (@lem6775123 A K _88612) (@lem6775122 A K)). Qed.
Lemma lem6775125 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775126 {A K : Type'} (_88612 : type849 A K) : (term134 A K _88612) = (term135 A K _88612).
Proof. exact (MK_COMB (@lem6775125) (@lem6775124 A K _88612)). Qed.
Lemma lem6775127 {A K : Type'} (k : K -> Prop) : (term63 A K k) = (term64 A K k).
Proof. exact (eq_refl (term63 A K k)). Qed.
Lemma lem6775128 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term65 A K _88612 k) = (term65 A K _88612 k).
Proof. exact (eq_refl (term65 A K _88612 k)). Qed.
Lemma lem6775129 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((_88612 k) = (term63 A K k)) = ((_88612 k) = (term64 A K k)).
Proof. exact (MK_COMB (@lem6775128 A K _88612 k) (@lem6775127 A K k)). Qed.
Lemma lem6775130 {A K : Type'} (_88612 : type849 A K) : (term136 A K _88612) = (term137 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775129 A K _88612 k)). Qed.
Lemma lem6775131 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6775132 {A K : Type'} (_88612 : type849 A K) : (term133 A K _88612) = (term138 A K _88612).
Proof. exact (MK_COMB (@lem6775131 K) (@lem6775130 A K _88612)). Qed.
Lemma lem6775133 {A K : Type'} (_88612 : type849 A K) : ((_88612 = (term132 A K)) = (term133 A K _88612)) = ((_88612 = (term62 A K)) = (term138 A K _88612)).
Proof. exact (MK_COMB (@lem6775126 A K _88612) (@lem6775132 A K _88612)). Qed.
Lemma lem6775134 {A K : Type'} (_88612 : type849 A K) : (_88612 = (term62 A K)) = (term138 A K _88612).
Proof. exact (EQ_MP (@lem6775133 A K _88612) (@lem6775120 A K _88612)). Qed.
Lemma lem6775136 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term128 _3571 _3575 t)) = (term129 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6775137 {A K : Type'} (s : type781 A K) (t : type781 A K) : (s = (term139 A K t)) = (term140 A K s t).
Proof. exact (@lem6775136 (type669 A K) (K -> A) s t). Qed.
Lemma lem6775138 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((_88612 k) = (term141 A K k)) = (term142 A K _88612 k).
Proof. exact (@lem6775137 A K (_88612 k) (term64 A K k)). Qed.
Lemma lem6775139 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term66 A K k f) = (term67 A K k f).
Proof. exact (eq_refl (term66 A K k f)). Qed.
Lemma lem6775140 {A K : Type'} (k : K -> Prop) : (term141 A K k) = (term64 A K k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775139 A K k f)). Qed.
Lemma lem6775141 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term65 A K _88612 k) = (term65 A K _88612 k).
Proof. exact (eq_refl (term65 A K _88612 k)). Qed.
Lemma lem6775142 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((_88612 k) = (term141 A K k)) = ((_88612 k) = (term64 A K k)).
Proof. exact (MK_COMB (@lem6775141 A K _88612 k) (@lem6775140 A K k)). Qed.
Lemma lem6775143 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775144 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term143 A K _88612 k) = (term144 A K _88612 k).
Proof. exact (MK_COMB (@lem6775143) (@lem6775142 A K _88612 k)). Qed.
Lemma lem6775145 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term66 A K k f) = (term67 A K k f).
Proof. exact (eq_refl (term66 A K k f)). Qed.
Lemma lem6775146 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term68 A K _88612 k f) = (term68 A K _88612 k f).
Proof. exact (eq_refl (term68 A K _88612 k f)). Qed.
Lemma lem6775147 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((_88612 k f) = (term66 A K k f)) = ((_88612 k f) = (term67 A K k f)).
Proof. exact (MK_COMB (@lem6775146 A K _88612 k f) (@lem6775145 A K k f)). Qed.
Lemma lem6775148 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term145 A K _88612 k) = (term146 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775147 A K _88612 k f)). Qed.
Lemma lem6775149 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775150 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term142 A K _88612 k) = (term147 A K _88612 k).
Proof. exact (MK_COMB (@lem6775149 A K) (@lem6775148 A K _88612 k)). Qed.
Lemma lem6775151 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (((_88612 k) = (term141 A K k)) = (term142 A K _88612 k)) = (((_88612 k) = (term64 A K k)) = (term147 A K _88612 k)).
Proof. exact (MK_COMB (@lem6775144 A K _88612 k) (@lem6775150 A K _88612 k)). Qed.
Lemma lem6775152 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((_88612 k) = (term64 A K k)) = (term147 A K _88612 k).
Proof. exact (EQ_MP (@lem6775151 A K _88612 k) (@lem6775138 A K _88612 k)). Qed.
Lemma lem6775154 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term128 _3571 _3575 t)) = (term129 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6775155 {A K : Type'} (s : type669 A K) (t : type669 A K) : (s = (term148 A K t)) = (term149 A K s t).
Proof. exact (@lem6775154 (type1413 A K) (A -> Prop) s t). Qed.
Lemma lem6775156 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((_88612 k f) = (term150 A K k f)) = (term151 A K _88612 k f).
Proof. exact (@lem6775155 A K (_88612 k f) (term67 A K k f)). Qed.
Lemma lem6775157 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term69 A K k f dom) = (term70 A K k f dom).
Proof. exact (eq_refl (term69 A K k f dom)). Qed.
Lemma lem6775158 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term150 A K k f) = (term67 A K k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775157 A K k f dom)). Qed.
Lemma lem6775159 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term68 A K _88612 k f) = (term68 A K _88612 k f).
Proof. exact (eq_refl (term68 A K _88612 k f)). Qed.
Lemma lem6775160 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((_88612 k f) = (term150 A K k f)) = ((_88612 k f) = (term67 A K k f)).
Proof. exact (MK_COMB (@lem6775159 A K _88612 k f) (@lem6775158 A K k f)). Qed.
Lemma lem6775161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775162 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term152 A K _88612 k f) = (term153 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775161) (@lem6775160 A K _88612 k f)). Qed.
Lemma lem6775163 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term69 A K k f dom) = (term70 A K k f dom).
Proof. exact (eq_refl (term69 A K k f dom)). Qed.
Lemma lem6775164 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term71 A K _88612 k f dom) = (term71 A K _88612 k f dom).
Proof. exact (eq_refl (term71 A K _88612 k f dom)). Qed.
Lemma lem6775165 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((_88612 k f dom) = (term69 A K k f dom)) = ((_88612 k f dom) = (term70 A K k f dom)).
Proof. exact (MK_COMB (@lem6775164 A K _88612 k f dom) (@lem6775163 A K k f dom)). Qed.
Lemma lem6775166 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term154 A K _88612 k f) = (term155 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775165 A K _88612 k f dom)). Qed.
Lemma lem6775167 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775168 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term151 A K _88612 k f) = (term156 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775167 A) (@lem6775166 A K _88612 k f)). Qed.
Lemma lem6775169 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (((_88612 k f) = (term150 A K k f)) = (term151 A K _88612 k f)) = (((_88612 k f) = (term67 A K k f)) = (term156 A K _88612 k f)).
Proof. exact (MK_COMB (@lem6775162 A K _88612 k f) (@lem6775168 A K _88612 k f)). Qed.
Lemma lem6775170 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((_88612 k f) = (term67 A K k f)) = (term156 A K _88612 k f).
Proof. exact (EQ_MP (@lem6775169 A K _88612 k f) (@lem6775156 A K _88612 k f)). Qed.
Lemma lem6775172 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term128 _3571 _3575 t)) = (term129 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6775173 {A K : Type'} (s : type1413 A K) (t : type1413 A K) : (s = (term157 A K t)) = (term158 A K s t).
Proof. exact (@lem6775172 (K -> Prop) A s t). Qed.
Lemma lem6775174 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((_88612 k f dom) = (term159 A K k f dom)) = (term160 A K _88612 k f dom).
Proof. exact (@lem6775173 A K (_88612 k f dom) (term70 A K k f dom)). Qed.
Lemma lem6775175 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term72 A K k f dom neut) = (term73 A K k f dom neut).
Proof. exact (eq_refl (term72 A K k f dom neut)). Qed.
Lemma lem6775176 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term159 A K k f dom) = (term70 A K k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775175 A K k f dom neut)). Qed.
Lemma lem6775177 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term71 A K _88612 k f dom) = (term71 A K _88612 k f dom).
Proof. exact (eq_refl (term71 A K _88612 k f dom)). Qed.
Lemma lem6775178 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((_88612 k f dom) = (term159 A K k f dom)) = ((_88612 k f dom) = (term70 A K k f dom)).
Proof. exact (MK_COMB (@lem6775177 A K _88612 k f dom) (@lem6775176 A K k f dom)). Qed.
Lemma lem6775179 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775180 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term161 A K _88612 k f dom) = (term162 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775179) (@lem6775178 A K _88612 k f dom)). Qed.
Lemma lem6775181 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term72 A K k f dom neut) = (term73 A K k f dom neut).
Proof. exact (eq_refl (term72 A K k f dom neut)). Qed.
Lemma lem6775182 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term74 A K _88612 k f dom neut) = (term74 A K _88612 k f dom neut).
Proof. exact (eq_refl (term74 A K _88612 k f dom neut)). Qed.
Lemma lem6775183 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut) = (term72 A K k f dom neut)) = ((_88612 k f dom neut) = (term73 A K k f dom neut)).
Proof. exact (MK_COMB (@lem6775182 A K _88612 k f dom neut) (@lem6775181 A K k f dom neut)). Qed.
Lemma lem6775184 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term163 A K _88612 k f dom) = (term164 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775183 A K _88612 k f dom neut)). Qed.
Lemma lem6775185 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775186 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term160 A K _88612 k f dom) = (term165 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775185 A) (@lem6775184 A K _88612 k f dom)). Qed.
Lemma lem6775187 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (((_88612 k f dom) = (term159 A K k f dom)) = (term160 A K _88612 k f dom)) = (((_88612 k f dom) = (term70 A K k f dom)) = (term165 A K _88612 k f dom)).
Proof. exact (MK_COMB (@lem6775180 A K _88612 k f dom) (@lem6775186 A K _88612 k f dom)). Qed.
Lemma lem6775188 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((_88612 k f dom) = (term70 A K k f dom)) = (term165 A K _88612 k f dom).
Proof. exact (EQ_MP (@lem6775187 A K _88612 k f dom) (@lem6775174 A K _88612 k f dom)). Qed.
Lemma lem6775190 {_3571 _3575 : Type'} (s : _3575 -> _3571) (t : _3575 -> _3571) : (s = (term128 _3571 _3575 t)) = (term129 _3571 _3575 s t).
Proof. exact (EQ_MP (@lem19792 _3571 _3575 s t) (@lem0)). Qed.
Lemma lem6775191 {K : Type'} (s : K -> Prop) (t : K -> Prop) : (s = (term166 K t)) = (term167 K s t).
Proof. exact (@lem6775190 Prop K s t). Qed.
Lemma lem6775192 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut) = (term168 A K k f dom neut)) = (term169 A K _88612 k f dom neut).
Proof. exact (@lem6775191 K (_88612 k f dom neut) (term73 A K k f dom neut)). Qed.
Lemma lem6775193 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term170 A K k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term170 A K k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775194 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term168 A K k f dom neut) = (term73 A K k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775193 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775195 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term74 A K _88612 k f dom neut) = (term74 A K _88612 k f dom neut).
Proof. exact (eq_refl (term74 A K _88612 k f dom neut)). Qed.
Lemma lem6775196 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut) = (term168 A K k f dom neut)) = ((_88612 k f dom neut) = (term73 A K k f dom neut)).
Proof. exact (MK_COMB (@lem6775195 A K _88612 k f dom neut) (@lem6775194 A K k f dom neut)). Qed.
Lemma lem6775197 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775198 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term172 A K _88612 k f dom neut) = (term173 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775197) (@lem6775196 A K _88612 k f dom neut)). Qed.
Lemma lem6775199 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term170 A K k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term170 A K k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775200 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_273 : K) : (term174 A K _88612 k f dom neut GEN_PVAR_273) = (term174 A K _88612 k f dom neut GEN_PVAR_273).
Proof. exact (eq_refl (term174 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775201 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut GEN_PVAR_273) = (term170 A K k f dom neut GEN_PVAR_273)) = ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)).
Proof. exact (MK_COMB (@lem6775200 A K _88612 k f dom neut GEN_PVAR_273) (@lem6775199 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775202 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term175 A K _88612 k f dom neut) = (term176 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775201 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775203 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775204 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term169 A K _88612 k f dom neut) = (term177 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775203 K) (@lem6775202 A K _88612 k f dom neut)). Qed.
Lemma lem6775205 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (((_88612 k f dom neut) = (term168 A K k f dom neut)) = (term169 A K _88612 k f dom neut)) = (((_88612 k f dom neut) = (term73 A K k f dom neut)) = (term177 A K _88612 k f dom neut)).
Proof. exact (MK_COMB (@lem6775198 A K _88612 k f dom neut) (@lem6775204 A K _88612 k f dom neut)). Qed.
Lemma lem6775206 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut) = (term73 A K k f dom neut)) = (term177 A K _88612 k f dom neut).
Proof. exact (EQ_MP (@lem6775205 A K _88612 k f dom neut) (@lem6775192 A K _88612 k f dom neut)). Qed.
Lemma lem6775207 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)) = ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)).
Proof. exact (eq_refl ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut))). Qed.
Lemma lem6775208 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term176 A K _88612 k f dom neut) = (term176 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775207 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775209 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775210 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term177 A K _88612 k f dom neut) = (term177 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775209 K) (@lem6775208 A K _88612 k f dom neut)). Qed.
Lemma lem6775211 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut) = (term73 A K k f dom neut)) = (term177 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6775206 A K _88612 k f dom neut) (@lem6775210 A K _88612 k f dom neut)). Qed.
Lemma lem6775212 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term164 A K _88612 k f dom) = (term178 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775211 A K _88612 k f dom neut)). Qed.
Lemma lem6775213 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775214 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term165 A K _88612 k f dom) = (term179 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775213 A) (@lem6775212 A K _88612 k f dom)). Qed.
Lemma lem6775215 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((_88612 k f dom) = (term70 A K k f dom)) = (term179 A K _88612 k f dom).
Proof. exact (TRANS (@lem6775188 A K _88612 k f dom) (@lem6775214 A K _88612 k f dom)). Qed.
Lemma lem6775216 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term155 A K _88612 k f) = (term180 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775215 A K _88612 k f dom)). Qed.
Lemma lem6775217 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775218 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term156 A K _88612 k f) = (term181 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775217 A) (@lem6775216 A K _88612 k f)). Qed.
Lemma lem6775219 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((_88612 k f) = (term67 A K k f)) = (term181 A K _88612 k f).
Proof. exact (TRANS (@lem6775170 A K _88612 k f) (@lem6775218 A K _88612 k f)). Qed.
Lemma lem6775220 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term146 A K _88612 k) = (term182 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775219 A K _88612 k f)). Qed.
Lemma lem6775221 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775222 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term147 A K _88612 k) = (term183 A K _88612 k).
Proof. exact (MK_COMB (@lem6775221 A K) (@lem6775220 A K _88612 k)). Qed.
Lemma lem6775223 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((_88612 k) = (term64 A K k)) = (term183 A K _88612 k).
Proof. exact (TRANS (@lem6775152 A K _88612 k) (@lem6775222 A K _88612 k)). Qed.
Lemma lem6775224 {A K : Type'} (_88612 : type849 A K) : (term137 A K _88612) = (term184 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775223 A K _88612 k)). Qed.
Lemma lem6775225 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6775226 {A K : Type'} (_88612 : type849 A K) : (term138 A K _88612) = (term185 A K _88612).
Proof. exact (MK_COMB (@lem6775225 K) (@lem6775224 A K _88612)). Qed.
Lemma lem6775227 {A K : Type'} (_88612 : type849 A K) : (_88612 = (term62 A K)) = (term185 A K _88612).
Proof. exact (TRANS (@lem6775134 A K _88612) (@lem6775226 A K _88612)). Qed.
Lemma lem6775228 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6775229 {A K : Type'} (_88612 : type849 A K) : (term114 A K _88612) = (term186 A K _88612).
Proof. exact (MK_COMB (@lem6775228) (@lem6775227 A K _88612)). Qed.
Lemma lem6775230 {A K : Type'} (_88612 : type849 A K) : (term105 A K _88612) = (term105 A K _88612).
Proof. exact (eq_refl (term105 A K _88612)). Qed.
Lemma lem6775231 {A K : Type'} (_88612 : type849 A K) : (term122 A K _88612) = (term187 A K _88612).
Proof. exact (MK_COMB (@lem6775229 A K _88612) (@lem6775230 A K _88612)). Qed.
Lemma lem6775232 {A K : Type'} : (term124 A K) = (term188 A K).
Proof. exact (fun_ext (fun _88612 : type849 A K => @lem6775231 A K _88612)). Qed.
Lemma lem6775233 {A K : Type'} : (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop))). Qed.
Lemma lem6775234 {A K : Type'} : (term126 A K) = (term189 A K).
Proof. exact (MK_COMB (@lem6775233 A K) (@lem6775232 A K)). Qed.
Lemma lem6775235 {A K : Type'} : (term113 A K) = (term113 A K).
Proof. exact (eq_refl (term113 A K)). Qed.
Lemma lem6775236 {A K : Type'} : ((term61 A K) = (term126 A K)) = ((term61 A K) = (term189 A K)).
Proof. exact (MK_COMB (@lem6775235 A K) (@lem6775234 A K)). Qed.
Lemma lem6775239 {A K : Type'} : (term61 A K) = (term189 A K).
Proof. exact (EQ_MP (@lem6775236 A K) (@lem6775116 A K)). Qed.
Lemma lem6775240 {A K : Type'} : (term60 A K) = (term189 A K).
Proof. exact (TRANS (@lem6774919 A K) (@lem6775239 A K)). Qed.
Lemma lem6775253 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term75 A K ltle k f dom neut j i) = (term75 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term75 A K ltle k f dom neut j i)). Qed.
Lemma lem6775254 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term76 A K ltle k f dom neut i) = (term76 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6775253 A K ltle k f dom neut j i)). Qed.
Lemma lem6775255 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775256 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term77 A K ltle k f dom neut i) = (term77 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775255 K) (@lem6775254 A K ltle k f dom neut i)). Qed.
Lemma lem6775269 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term78 K k ltle j i) = (term78 K k ltle j i).
Proof. exact (eq_refl (term78 K k ltle j i)). Qed.
Lemma lem6775270 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term79 K k ltle i) = (term79 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6775269 K k ltle j i)). Qed.
Lemma lem6775271 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775272 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term80 K k ltle i) = (term80 K k ltle i).
Proof. exact (MK_COMB (@lem6775271 K) (@lem6775270 K k ltle i)). Qed.
Lemma lem6775273 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775274 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term81 K k ltle i) = (term81 K k ltle i).
Proof. exact (MK_COMB (@lem6775273) (@lem6775272 K k ltle i)). Qed.
Lemma lem6775275 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term82 A K ltle k f dom neut i) = (term82 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775274 K k ltle i) (@lem6775256 A K ltle k f dom neut i)). Qed.
Lemma lem6775278 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term87 A K _88612 k f dom neut) = (term87 A K _88612 k f dom neut).
Proof. exact (eq_refl (term87 A K _88612 k f dom neut)). Qed.
Lemma lem6775279 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term88 A K _88612 ltle k f dom neut i) = (term88 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775278 A K _88612 k f dom neut) (@lem6775275 A K ltle k f dom neut i)). Qed.
Lemma lem6775290 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term89 K k ltle j i) = (term89 K k ltle j i).
Proof. exact (eq_refl (term89 K k ltle j i)). Qed.
Lemma lem6775291 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term90 K k ltle i) = (term90 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6775290 K k ltle j i)). Qed.
Lemma lem6775292 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775293 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term21 K k ltle i) = (term21 K k ltle i).
Proof. exact (MK_COMB (@lem6775292 K) (@lem6775291 K k ltle i)). Qed.
Lemma lem6775294 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6775295 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term33 K k ltle i) = (term33 K k ltle i).
Proof. exact (MK_COMB (@lem6775294) (@lem6775293 K k ltle i)). Qed.
Lemma lem6775296 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term91 A K _88612 ltle k f dom neut i) = (term91 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775295 K k ltle i) (@lem6775279 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6775299 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term92 A K _88612 k f dom neut) = (term92 A K _88612 k f dom neut).
Proof. exact (eq_refl (term92 A K _88612 k f dom neut)). Qed.
Lemma lem6775300 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term93 A K _88612 ltle k f dom neut i) = (term93 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6775299 A K _88612 k f dom neut) (@lem6775296 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6775301 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term94 A K _88612 k f dom neut i) = (term94 A K _88612 k f dom neut i).
Proof. exact (fun_ext (fun ltle : type1402 K => @lem6775300 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6775302 {K : Type'} : (@all (K -> K -> Prop)) = (@all (K -> K -> Prop)).
Proof. exact (eq_refl (@all (K -> K -> Prop))). Qed.
Lemma lem6775303 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term95 A K _88612 k f dom neut i) = (term95 A K _88612 k f dom neut i).
Proof. exact (MK_COMB (@lem6775302 K) (@lem6775301 A K _88612 k f dom neut i)). Qed.
Lemma lem6775304 {A K : Type'} (_88612 : type849 A K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term96 A K _88612 f dom neut i) = (term96 A K _88612 f dom neut i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775303 A K _88612 k f dom neut i)). Qed.
Lemma lem6775305 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6775306 {A K : Type'} (_88612 : type849 A K) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term97 A K _88612 f dom neut i) = (term97 A K _88612 f dom neut i).
Proof. exact (MK_COMB (@lem6775305 K) (@lem6775304 A K _88612 f dom neut i)). Qed.
Lemma lem6775307 {A K : Type'} (_88612 : type849 A K) (dom : A -> Prop) (neut : A) (i : K) : (term98 A K _88612 dom neut i) = (term98 A K _88612 dom neut i).
Proof. exact (fun_ext (fun f : K -> A => @lem6775306 A K _88612 f dom neut i)). Qed.
Lemma lem6775308 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775309 {A K : Type'} (_88612 : type849 A K) (dom : A -> Prop) (neut : A) (i : K) : (term99 A K _88612 dom neut i) = (term99 A K _88612 dom neut i).
Proof. exact (MK_COMB (@lem6775308 A K) (@lem6775307 A K _88612 dom neut i)). Qed.
Lemma lem6775310 {A K : Type'} (_88612 : type849 A K) (neut : A) (i : K) : (term100 A K _88612 neut i) = (term100 A K _88612 neut i).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775309 A K _88612 dom neut i)). Qed.
Lemma lem6775311 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775312 {A K : Type'} (_88612 : type849 A K) (neut : A) (i : K) : (term101 A K _88612 neut i) = (term101 A K _88612 neut i).
Proof. exact (MK_COMB (@lem6775311 A) (@lem6775310 A K _88612 neut i)). Qed.
Lemma lem6775313 {A K : Type'} (_88612 : type849 A K) (i : K) : (term102 A K _88612 i) = (term102 A K _88612 i).
Proof. exact (fun_ext (fun neut : A => @lem6775312 A K _88612 neut i)). Qed.
Lemma lem6775314 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775315 {A K : Type'} (_88612 : type849 A K) (i : K) : (term103 A K _88612 i) = (term103 A K _88612 i).
Proof. exact (MK_COMB (@lem6775314 A) (@lem6775313 A K _88612 i)). Qed.
Lemma lem6775316 {A K : Type'} (_88612 : type849 A K) : (term104 A K _88612) = (term104 A K _88612).
Proof. exact (fun_ext (fun i : K => @lem6775315 A K _88612 i)). Qed.
Lemma lem6775317 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775318 {A K : Type'} (_88612 : type849 A K) : (term105 A K _88612) = (term105 A K _88612).
Proof. exact (MK_COMB (@lem6775317 K) (@lem6775316 A K _88612)). Qed.
Lemma lem6775319 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term190 A K GEN_PVAR_273 k f dom neut i) = (term190 A K GEN_PVAR_273 k f dom neut i).
Proof. exact (eq_refl (term190 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775320 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term191 A K GEN_PVAR_273 k f dom neut) = (term191 A K GEN_PVAR_273 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6775319 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775321 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6775322 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term171 A K GEN_PVAR_273 k f dom neut) = (term171 A K GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775321 K) (@lem6775320 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775325 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_273 : K) : (term174 A K _88612 k f dom neut GEN_PVAR_273) = (term174 A K _88612 k f dom neut GEN_PVAR_273).
Proof. exact (eq_refl (term174 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775326 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)) = ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)).
Proof. exact (MK_COMB (@lem6775325 A K _88612 k f dom neut GEN_PVAR_273) (@lem6775322 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775327 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term176 A K _88612 k f dom neut) = (term176 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775326 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775328 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775329 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term177 A K _88612 k f dom neut) = (term177 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775328 K) (@lem6775327 A K _88612 k f dom neut)). Qed.
Lemma lem6775330 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term178 A K _88612 k f dom) = (term178 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775329 A K _88612 k f dom neut)). Qed.
Lemma lem6775331 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775332 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term179 A K _88612 k f dom) = (term179 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775331 A) (@lem6775330 A K _88612 k f dom)). Qed.
Lemma lem6775333 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term180 A K _88612 k f) = (term180 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775332 A K _88612 k f dom)). Qed.
Lemma lem6775334 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775335 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term181 A K _88612 k f) = (term181 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775334 A) (@lem6775333 A K _88612 k f)). Qed.
Lemma lem6775336 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term182 A K _88612 k) = (term182 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775335 A K _88612 k f)). Qed.
Lemma lem6775337 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775338 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term183 A K _88612 k) = (term183 A K _88612 k).
Proof. exact (MK_COMB (@lem6775337 A K) (@lem6775336 A K _88612 k)). Qed.
Lemma lem6775339 {A K : Type'} (_88612 : type849 A K) : (term184 A K _88612) = (term184 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775338 A K _88612 k)). Qed.
Lemma lem6775340 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6775341 {A K : Type'} (_88612 : type849 A K) : (term185 A K _88612) = (term185 A K _88612).
Proof. exact (MK_COMB (@lem6775340 K) (@lem6775339 A K _88612)). Qed.
Lemma lem6775342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6775343 {A K : Type'} (_88612 : type849 A K) : (term186 A K _88612) = (term186 A K _88612).
Proof. exact (MK_COMB (@lem6775342) (@lem6775341 A K _88612)). Qed.
Lemma lem6775344 {A K : Type'} (_88612 : type849 A K) : (term187 A K _88612) = (term187 A K _88612).
Proof. exact (MK_COMB (@lem6775343 A K _88612) (@lem6775318 A K _88612)). Qed.
Lemma lem6775345 {A K : Type'} : (term188 A K) = (term188 A K).
Proof. exact (fun_ext (fun _88612 : type849 A K => @lem6775344 A K _88612)). Qed.
Lemma lem6775346 {A K : Type'} : (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)) = (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop)).
Proof. exact (eq_refl (@all ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop))). Qed.
Lemma lem6775347 {A K : Type'} : (term189 A K) = (term189 A K).
Proof. exact (MK_COMB (@lem6775346 A K) (@lem6775345 A K)). Qed.
Lemma lem6775474 {A K : Type'} : (term60 A K) = (term189 A K).
Proof. exact (TRANS (@lem6775240 A K) (@lem6775347 A K)). Qed.
Lemma lem6775475 {A K : Type'} : (term189 A K) = (term60 A K).
Proof. exact (SYM (@lem6775474 A K)). Qed.
Lemma lem6775476 {A K : Type'} (_88612 : type849 A K) (h1 : term185 A K _88612) : term185 A K _88612.
Proof. exact (h1). Qed.
Lemma lem6775478 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term21 K k ltle i.
Proof. exact (h1). Qed.
Lemma lem6775480 (p : Prop) : p = (term24 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem6775481 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term88 A K _88612 ltle k f dom neut i) = (term192 A K _88612 ltle k f dom neut i).
Proof. exact (@lem6775480 (term88 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6775482 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term192 A K _88612 ltle k f dom neut i) = (term88 A K _88612 ltle k f dom neut i).
Proof. exact (SYM (@lem6775481 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6775483 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term193 A K _88612 ltle k f dom neut i) : term193 A K _88612 ltle k f dom neut i.
Proof. exact (h1). Qed.
Lemma lem6775487 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term190 A K GEN_PVAR_273 k f dom neut i) = (term190 A K GEN_PVAR_273 k f dom neut i).
Proof. exact (eq_refl (term190 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775488 {K : Type'} (P : K -> Prop) : (term194 K P) = (term195 K P).
Proof. exact (@lem18394 K P). Qed.
Lemma lem6775489 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term196 A K GEN_PVAR_273 k f dom neut) = (term197 A K GEN_PVAR_273 k f dom neut).
Proof. exact (@lem6775488 K (term191 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775490 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term198 A K GEN_PVAR_273 k f dom neut i) = (term190 A K GEN_PVAR_273 k f dom neut i).
Proof. exact (eq_refl (term198 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775491 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6775493 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term199 A K GEN_PVAR_273 k f dom neut i) = (term200 A K GEN_PVAR_273 k f dom neut i).
Proof. exact (MK_COMB (@lem6775491) (@lem6775490 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775494 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term201 A K GEN_PVAR_273 k f dom neut) = (term202 A K GEN_PVAR_273 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6775493 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775495 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775496 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term197 A K GEN_PVAR_273 k f dom neut) = (term203 A K GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775495 K) (@lem6775494 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775497 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term196 A K GEN_PVAR_273 k f dom neut) = (term203 A K GEN_PVAR_273 k f dom neut).
Proof. exact (TRANS (@lem6775489 A K GEN_PVAR_273 k f dom neut) (@lem6775496 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775498 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term191 A K GEN_PVAR_273 k f dom neut) = (term191 A K GEN_PVAR_273 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6775487 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6775499 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6775500 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term171 A K GEN_PVAR_273 k f dom neut) = (term171 A K GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775499 K) (@lem6775498 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775502 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_273 : K) : (term204 A K _88612 k f dom neut GEN_PVAR_273) = (term204 A K _88612 k f dom neut GEN_PVAR_273).
Proof. exact (eq_refl (term204 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775503 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term205 A K _88612 GEN_PVAR_273 k f dom neut) = (term205 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775502 A K _88612 k f dom neut GEN_PVAR_273) (@lem6775500 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775505 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_273 : K) : (term206 A K _88612 k f dom neut GEN_PVAR_273) = (term206 A K _88612 k f dom neut GEN_PVAR_273).
Proof. exact (eq_refl (term206 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775506 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term207 A K _88612 GEN_PVAR_273 k f dom neut) = (term208 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775505 A K _88612 k f dom neut GEN_PVAR_273) (@lem6775497 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775508 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term209 A K _88612 GEN_PVAR_273 k f dom neut) = (term210 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775507) (@lem6775506 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775509 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term211 A K _88612 GEN_PVAR_273 k f dom neut) = (term212 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775508 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6775503 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775510 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)) = (term211 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (@lem17784 (_88612 k f dom neut GEN_PVAR_273) (term171 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775511 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((_88612 k f dom neut GEN_PVAR_273) = (term171 A K GEN_PVAR_273 k f dom neut)) = (term212 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (TRANS (@lem6775510 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6775509 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775512 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term176 A K _88612 k f dom neut) = (term213 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775511 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775513 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775514 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term177 A K _88612 k f dom neut) = (term214 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775513 K) (@lem6775512 A K _88612 k f dom neut)). Qed.
Lemma lem6775515 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term178 A K _88612 k f dom) = (term215 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775514 A K _88612 k f dom neut)). Qed.
Lemma lem6775516 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775517 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term179 A K _88612 k f dom) = (term216 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775516 A) (@lem6775515 A K _88612 k f dom)). Qed.
Lemma lem6775518 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term180 A K _88612 k f) = (term217 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775517 A K _88612 k f dom)). Qed.
Lemma lem6775519 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775520 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term181 A K _88612 k f) = (term218 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775519 A) (@lem6775518 A K _88612 k f)). Qed.
Lemma lem6775521 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term182 A K _88612 k) = (term219 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775520 A K _88612 k f)). Qed.
Lemma lem6775522 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775523 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term183 A K _88612 k) = (term220 A K _88612 k).
Proof. exact (MK_COMB (@lem6775522 A K) (@lem6775521 A K _88612 k)). Qed.
Lemma lem6775524 {A K : Type'} (_88612 : type849 A K) : (term184 A K _88612) = (term221 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6775523 A K _88612 k)). Qed.
Lemma lem6775525 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6775526 {A K : Type'} (_88612 : type849 A K) : (term185 A K _88612) = (term222 A K _88612).
Proof. exact (MK_COMB (@lem6775525 K) (@lem6775524 A K _88612)). Qed.
Lemma lem6775544 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6775545 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term223 K P Q) = (term224 K P Q).
Proof. exact (@lem6775544 K P Q). Qed.
Lemma lem6775546 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term225 A K _88612 k f dom neut) = (term226 A K _88612 k f dom neut).
Proof. exact (@lem6775545 K (term227 A K _88612 k f dom neut) (term228 A K _88612 k f dom neut)). Qed.
Lemma lem6775547 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term229 A K _88612 k f dom neut GEN_PVAR_273) = (term208 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term229 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775549 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term230 A K _88612 k f dom neut GEN_PVAR_273) = (term210 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775548) (@lem6775547 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775550 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term231 A K _88612 k f dom neut GEN_PVAR_273) = (term205 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term231 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775551 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term232 A K _88612 k f dom neut GEN_PVAR_273) = (term212 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6775549 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6775550 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775552 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term233 A K _88612 k f dom neut) = (term213 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775551 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775553 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775554 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term225 A K _88612 k f dom neut) = (term214 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775553 K) (@lem6775552 A K _88612 k f dom neut)). Qed.
Lemma lem6775555 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775556 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term234 A K _88612 k f dom neut) = (term235 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775555) (@lem6775554 A K _88612 k f dom neut)). Qed.
Lemma lem6775557 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term229 A K _88612 k f dom neut GEN_PVAR_273) = (term208 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term229 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775558 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term236 A K _88612 k f dom neut) = (term227 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775557 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775559 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775560 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term237 A K _88612 k f dom neut) = (term238 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775559 K) (@lem6775558 A K _88612 k f dom neut)). Qed.
Lemma lem6775561 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775562 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term239 A K _88612 k f dom neut) = (term240 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775561) (@lem6775560 A K _88612 k f dom neut)). Qed.
Lemma lem6775563 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term231 A K _88612 k f dom neut GEN_PVAR_273) = (term205 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term231 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6775564 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term241 A K _88612 k f dom neut) = (term228 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6775563 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6775565 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6775566 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term242 A K _88612 k f dom neut) = (term243 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775565 K) (@lem6775564 A K _88612 k f dom neut)). Qed.
Lemma lem6775567 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term226 A K _88612 k f dom neut) = (term244 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775562 A K _88612 k f dom neut) (@lem6775566 A K _88612 k f dom neut)). Qed.
Lemma lem6775568 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term225 A K _88612 k f dom neut) = (term226 A K _88612 k f dom neut)) = ((term214 A K _88612 k f dom neut) = (term244 A K _88612 k f dom neut)).
Proof. exact (MK_COMB (@lem6775556 A K _88612 k f dom neut) (@lem6775567 A K _88612 k f dom neut)). Qed.
Lemma lem6775569 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term214 A K _88612 k f dom neut) = (term244 A K _88612 k f dom neut).
Proof. exact (EQ_MP (@lem6775568 A K _88612 k f dom neut) (@lem6775546 A K _88612 k f dom neut)). Qed.
Lemma lem6775674 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term215 A K _88612 k f dom) = (term245 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775569 A K _88612 k f dom neut)). Qed.
Lemma lem6775675 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775676 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term216 A K _88612 k f dom) = (term246 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775675 A) (@lem6775674 A K _88612 k f dom)). Qed.
Lemma lem6775678 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6775679 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (@lem6775678 A P Q). Qed.
Lemma lem6775680 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term247 A K _88612 k f dom) = (term248 A K _88612 k f dom).
Proof. exact (@lem6775679 A (term249 A K _88612 k f dom) (term250 A K _88612 k f dom)). Qed.
Lemma lem6775681 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term251 A K _88612 k f dom neut) = (term238 A K _88612 k f dom neut).
Proof. exact (eq_refl (term251 A K _88612 k f dom neut)). Qed.
Lemma lem6775682 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775683 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term252 A K _88612 k f dom neut) = (term240 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775682) (@lem6775681 A K _88612 k f dom neut)). Qed.
Lemma lem6775684 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term253 A K _88612 k f dom neut) = (term243 A K _88612 k f dom neut).
Proof. exact (eq_refl (term253 A K _88612 k f dom neut)). Qed.
Lemma lem6775685 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term254 A K _88612 k f dom neut) = (term244 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6775683 A K _88612 k f dom neut) (@lem6775684 A K _88612 k f dom neut)). Qed.
Lemma lem6775686 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term255 A K _88612 k f dom) = (term245 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775685 A K _88612 k f dom neut)). Qed.
Lemma lem6775687 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775688 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term247 A K _88612 k f dom) = (term246 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775687 A) (@lem6775686 A K _88612 k f dom)). Qed.
Lemma lem6775689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775690 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term256 A K _88612 k f dom) = (term257 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775689) (@lem6775688 A K _88612 k f dom)). Qed.
Lemma lem6775691 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term251 A K _88612 k f dom neut) = (term238 A K _88612 k f dom neut).
Proof. exact (eq_refl (term251 A K _88612 k f dom neut)). Qed.
Lemma lem6775692 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term258 A K _88612 k f dom) = (term249 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775691 A K _88612 k f dom neut)). Qed.
Lemma lem6775693 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775694 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term259 A K _88612 k f dom) = (term260 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775693 A) (@lem6775692 A K _88612 k f dom)). Qed.
Lemma lem6775695 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775696 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term261 A K _88612 k f dom) = (term262 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775695) (@lem6775694 A K _88612 k f dom)). Qed.
Lemma lem6775697 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term253 A K _88612 k f dom neut) = (term243 A K _88612 k f dom neut).
Proof. exact (eq_refl (term253 A K _88612 k f dom neut)). Qed.
Lemma lem6775698 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term263 A K _88612 k f dom) = (term250 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6775697 A K _88612 k f dom neut)). Qed.
Lemma lem6775699 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6775700 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term264 A K _88612 k f dom) = (term265 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775699 A) (@lem6775698 A K _88612 k f dom)). Qed.
Lemma lem6775701 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term248 A K _88612 k f dom) = (term266 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775696 A K _88612 k f dom) (@lem6775700 A K _88612 k f dom)). Qed.
Lemma lem6775702 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((term247 A K _88612 k f dom) = (term248 A K _88612 k f dom)) = ((term246 A K _88612 k f dom) = (term266 A K _88612 k f dom)).
Proof. exact (MK_COMB (@lem6775690 A K _88612 k f dom) (@lem6775701 A K _88612 k f dom)). Qed.
Lemma lem6775703 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term246 A K _88612 k f dom) = (term266 A K _88612 k f dom).
Proof. exact (EQ_MP (@lem6775702 A K _88612 k f dom) (@lem6775680 A K _88612 k f dom)). Qed.
Lemma lem6775816 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term216 A K _88612 k f dom) = (term266 A K _88612 k f dom).
Proof. exact (TRANS (@lem6775676 A K _88612 k f dom) (@lem6775703 A K _88612 k f dom)). Qed.
Lemma lem6775817 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term217 A K _88612 k f) = (term267 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775816 A K _88612 k f dom)). Qed.
Lemma lem6775818 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775819 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term218 A K _88612 k f) = (term268 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775818 A) (@lem6775817 A K _88612 k f)). Qed.
Lemma lem6775821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6775822 {A : Type'} (P : type686 A) (Q : type686 A) : (term269 A P Q) = (term270 A P Q).
Proof. exact (@lem6775821 (A -> Prop) P Q). Qed.
Lemma lem6775823 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term271 A K _88612 k f) = (term272 A K _88612 k f).
Proof. exact (@lem6775822 A (term273 A K _88612 k f) (term274 A K _88612 k f)). Qed.
Lemma lem6775824 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term275 A K _88612 k f dom) = (term260 A K _88612 k f dom).
Proof. exact (eq_refl (term275 A K _88612 k f dom)). Qed.
Lemma lem6775825 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775826 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term276 A K _88612 k f dom) = (term262 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775825) (@lem6775824 A K _88612 k f dom)). Qed.
Lemma lem6775827 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term277 A K _88612 k f dom) = (term265 A K _88612 k f dom).
Proof. exact (eq_refl (term277 A K _88612 k f dom)). Qed.
Lemma lem6775828 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term278 A K _88612 k f dom) = (term266 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6775826 A K _88612 k f dom) (@lem6775827 A K _88612 k f dom)). Qed.
Lemma lem6775829 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term279 A K _88612 k f) = (term267 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775828 A K _88612 k f dom)). Qed.
Lemma lem6775830 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775831 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term271 A K _88612 k f) = (term268 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775830 A) (@lem6775829 A K _88612 k f)). Qed.
Lemma lem6775832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775833 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term280 A K _88612 k f) = (term281 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775832) (@lem6775831 A K _88612 k f)). Qed.
Lemma lem6775834 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term275 A K _88612 k f dom) = (term260 A K _88612 k f dom).
Proof. exact (eq_refl (term275 A K _88612 k f dom)). Qed.
Lemma lem6775835 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term282 A K _88612 k f) = (term273 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775834 A K _88612 k f dom)). Qed.
Lemma lem6775836 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775837 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term283 A K _88612 k f) = (term284 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775836 A) (@lem6775835 A K _88612 k f)). Qed.
Lemma lem6775838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775839 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term285 A K _88612 k f) = (term286 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775838) (@lem6775837 A K _88612 k f)). Qed.
Lemma lem6775840 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term277 A K _88612 k f dom) = (term265 A K _88612 k f dom).
Proof. exact (eq_refl (term277 A K _88612 k f dom)). Qed.
Lemma lem6775841 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term287 A K _88612 k f) = (term274 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6775840 A K _88612 k f dom)). Qed.
Lemma lem6775842 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6775843 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term288 A K _88612 k f) = (term289 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775842 A) (@lem6775841 A K _88612 k f)). Qed.
Lemma lem6775844 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term272 A K _88612 k f) = (term290 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775839 A K _88612 k f) (@lem6775843 A K _88612 k f)). Qed.
Lemma lem6775845 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((term271 A K _88612 k f) = (term272 A K _88612 k f)) = ((term268 A K _88612 k f) = (term290 A K _88612 k f)).
Proof. exact (MK_COMB (@lem6775833 A K _88612 k f) (@lem6775844 A K _88612 k f)). Qed.
Lemma lem6775846 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term268 A K _88612 k f) = (term290 A K _88612 k f).
Proof. exact (EQ_MP (@lem6775845 A K _88612 k f) (@lem6775823 A K _88612 k f)). Qed.
Lemma lem6775967 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term218 A K _88612 k f) = (term290 A K _88612 k f).
Proof. exact (TRANS (@lem6775819 A K _88612 k f) (@lem6775846 A K _88612 k f)). Qed.
Lemma lem6775968 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term219 A K _88612 k) = (term291 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775967 A K _88612 k f)). Qed.
Lemma lem6775969 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775970 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term220 A K _88612 k) = (term292 A K _88612 k).
Proof. exact (MK_COMB (@lem6775969 A K) (@lem6775968 A K _88612 k)). Qed.
Lemma lem6775972 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6775973 {A K : Type'} (P : type805 A K) (Q : type805 A K) : (term293 A K P Q) = (term294 A K P Q).
Proof. exact (@lem6775972 (K -> A) P Q). Qed.
Lemma lem6775974 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term295 A K _88612 k) = (term296 A K _88612 k).
Proof. exact (@lem6775973 A K (term297 A K _88612 k) (term298 A K _88612 k)). Qed.
Lemma lem6775975 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term299 A K _88612 k f) = (term284 A K _88612 k f).
Proof. exact (eq_refl (term299 A K _88612 k f)). Qed.
Lemma lem6775976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775977 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term300 A K _88612 k f) = (term286 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775976) (@lem6775975 A K _88612 k f)). Qed.
Lemma lem6775978 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term301 A K _88612 k f) = (term289 A K _88612 k f).
Proof. exact (eq_refl (term301 A K _88612 k f)). Qed.
Lemma lem6775979 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term302 A K _88612 k f) = (term290 A K _88612 k f).
Proof. exact (MK_COMB (@lem6775977 A K _88612 k f) (@lem6775978 A K _88612 k f)). Qed.
Lemma lem6775980 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term303 A K _88612 k) = (term291 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775979 A K _88612 k f)). Qed.
Lemma lem6775981 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775982 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term295 A K _88612 k) = (term292 A K _88612 k).
Proof. exact (MK_COMB (@lem6775981 A K) (@lem6775980 A K _88612 k)). Qed.
Lemma lem6775983 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6775984 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term304 A K _88612 k) = (term305 A K _88612 k).
Proof. exact (MK_COMB (@lem6775983) (@lem6775982 A K _88612 k)). Qed.
Lemma lem6775985 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term299 A K _88612 k f) = (term284 A K _88612 k f).
Proof. exact (eq_refl (term299 A K _88612 k f)). Qed.
Lemma lem6775986 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term306 A K _88612 k) = (term297 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775985 A K _88612 k f)). Qed.
Lemma lem6775987 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775988 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term307 A K _88612 k) = (term308 A K _88612 k).
Proof. exact (MK_COMB (@lem6775987 A K) (@lem6775986 A K _88612 k)). Qed.
Lemma lem6775989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6775990 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term309 A K _88612 k) = (term310 A K _88612 k).
Proof. exact (MK_COMB (@lem6775989) (@lem6775988 A K _88612 k)). Qed.
Lemma lem6775991 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term301 A K _88612 k f) = (term289 A K _88612 k f).
Proof. exact (eq_refl (term301 A K _88612 k f)). Qed.
Lemma lem6775992 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term311 A K _88612 k) = (term298 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6775991 A K _88612 k f)). Qed.
Lemma lem6775993 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6775994 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term312 A K _88612 k) = (term313 A K _88612 k).
Proof. exact (MK_COMB (@lem6775993 A K) (@lem6775992 A K _88612 k)). Qed.
Lemma lem6775995 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term296 A K _88612 k) = (term314 A K _88612 k).
Proof. exact (MK_COMB (@lem6775990 A K _88612 k) (@lem6775994 A K _88612 k)). Qed.
Lemma lem6775996 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((term295 A K _88612 k) = (term296 A K _88612 k)) = ((term292 A K _88612 k) = (term314 A K _88612 k)).
Proof. exact (MK_COMB (@lem6775984 A K _88612 k) (@lem6775995 A K _88612 k)). Qed.
Lemma lem6775997 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term292 A K _88612 k) = (term314 A K _88612 k).
Proof. exact (EQ_MP (@lem6775996 A K _88612 k) (@lem6775974 A K _88612 k)). Qed.
Lemma lem6776126 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term220 A K _88612 k) = (term314 A K _88612 k).
Proof. exact (TRANS (@lem6775970 A K _88612 k) (@lem6775997 A K _88612 k)). Qed.
Lemma lem6776127 {A K : Type'} (_88612 : type849 A K) : (term221 A K _88612) = (term315 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776126 A K _88612 k)). Qed.
Lemma lem6776128 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776129 {A K : Type'} (_88612 : type849 A K) : (term222 A K _88612) = (term316 A K _88612).
Proof. exact (MK_COMB (@lem6776128 K) (@lem6776127 A K _88612)). Qed.
Lemma lem6776131 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term223 A P Q) = (term224 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem6776132 {K : Type'} (P : type686 K) (Q : type686 K) : (term269 K P Q) = (term270 K P Q).
Proof. exact (@lem6776131 (K -> Prop) P Q). Qed.
Lemma lem6776133 {A K : Type'} (_88612 : type849 A K) : (term317 A K _88612) = (term318 A K _88612).
Proof. exact (@lem6776132 K (term319 A K _88612) (term320 A K _88612)). Qed.
Lemma lem6776134 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term321 A K _88612 k) = (term308 A K _88612 k).
Proof. exact (eq_refl (term321 A K _88612 k)). Qed.
Lemma lem6776135 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6776136 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term322 A K _88612 k) = (term310 A K _88612 k).
Proof. exact (MK_COMB (@lem6776135) (@lem6776134 A K _88612 k)). Qed.
Lemma lem6776137 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term323 A K _88612 k) = (term313 A K _88612 k).
Proof. exact (eq_refl (term323 A K _88612 k)). Qed.
Lemma lem6776138 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term324 A K _88612 k) = (term314 A K _88612 k).
Proof. exact (MK_COMB (@lem6776136 A K _88612 k) (@lem6776137 A K _88612 k)). Qed.
Lemma lem6776139 {A K : Type'} (_88612 : type849 A K) : (term325 A K _88612) = (term315 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776138 A K _88612 k)). Qed.
Lemma lem6776140 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776141 {A K : Type'} (_88612 : type849 A K) : (term317 A K _88612) = (term316 A K _88612).
Proof. exact (MK_COMB (@lem6776140 K) (@lem6776139 A K _88612)). Qed.
Lemma lem6776142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776143 {A K : Type'} (_88612 : type849 A K) : (term326 A K _88612) = (term327 A K _88612).
Proof. exact (MK_COMB (@lem6776142) (@lem6776141 A K _88612)). Qed.
Lemma lem6776144 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term321 A K _88612 k) = (term308 A K _88612 k).
Proof. exact (eq_refl (term321 A K _88612 k)). Qed.
Lemma lem6776145 {A K : Type'} (_88612 : type849 A K) : (term328 A K _88612) = (term319 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776144 A K _88612 k)). Qed.
Lemma lem6776146 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776147 {A K : Type'} (_88612 : type849 A K) : (term329 A K _88612) = (term330 A K _88612).
Proof. exact (MK_COMB (@lem6776146 K) (@lem6776145 A K _88612)). Qed.
Lemma lem6776148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6776149 {A K : Type'} (_88612 : type849 A K) : (term331 A K _88612) = (term332 A K _88612).
Proof. exact (MK_COMB (@lem6776148) (@lem6776147 A K _88612)). Qed.
Lemma lem6776150 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term323 A K _88612 k) = (term313 A K _88612 k).
Proof. exact (eq_refl (term323 A K _88612 k)). Qed.
Lemma lem6776151 {A K : Type'} (_88612 : type849 A K) : (term333 A K _88612) = (term320 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776150 A K _88612 k)). Qed.
Lemma lem6776152 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776153 {A K : Type'} (_88612 : type849 A K) : (term334 A K _88612) = (term335 A K _88612).
Proof. exact (MK_COMB (@lem6776152 K) (@lem6776151 A K _88612)). Qed.
Lemma lem6776154 {A K : Type'} (_88612 : type849 A K) : (term318 A K _88612) = (term336 A K _88612).
Proof. exact (MK_COMB (@lem6776149 A K _88612) (@lem6776153 A K _88612)). Qed.
Lemma lem6776155 {A K : Type'} (_88612 : type849 A K) : ((term317 A K _88612) = (term318 A K _88612)) = ((term316 A K _88612) = (term336 A K _88612)).
Proof. exact (MK_COMB (@lem6776143 A K _88612) (@lem6776154 A K _88612)). Qed.
Lemma lem6776156 {A K : Type'} (_88612 : type849 A K) : (term316 A K _88612) = (term336 A K _88612).
Proof. exact (EQ_MP (@lem6776155 A K _88612) (@lem6776133 A K _88612)). Qed.
Lemma lem6776293 {A K : Type'} (_88612 : type849 A K) : (term222 A K _88612) = (term336 A K _88612).
Proof. exact (TRANS (@lem6776129 A K _88612) (@lem6776156 A K _88612)). Qed.
Lemma lem6776295 {A : Type'} (P : Prop) (Q : A -> Prop) : (term337 A P Q) = (term338 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6776296 {K : Type'} (P : Prop) (Q : K -> Prop) : (term337 K P Q) = (term338 K P Q).
Proof. exact (@lem6776295 K P Q). Qed.
Lemma lem6776297 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term339 A K _88612 GEN_PVAR_273 k f dom neut) = (term340 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (@lem6776296 K (term341 A K _88612 k f dom neut GEN_PVAR_273) (term191 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776298 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term198 A K GEN_PVAR_273 k f dom neut i) = (term190 A K GEN_PVAR_273 k f dom neut i).
Proof. exact (eq_refl (term198 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776299 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term342 A K GEN_PVAR_273 k f dom neut) = (term191 A K GEN_PVAR_273 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6776298 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776300 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776301 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term343 A K GEN_PVAR_273 k f dom neut) = (term171 A K GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6776300 K) (@lem6776299 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776302 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_273 : K) : (term204 A K _88612 k f dom neut GEN_PVAR_273) = (term204 A K _88612 k f dom neut GEN_PVAR_273).
Proof. exact (eq_refl (term204 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6776303 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term339 A K _88612 GEN_PVAR_273 k f dom neut) = (term205 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6776302 A K _88612 k f dom neut GEN_PVAR_273) (@lem6776301 A K GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776305 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term344 A K _88612 GEN_PVAR_273 k f dom neut) = (term345 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6776304) (@lem6776303 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776306 {A K : Type'} (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term198 A K GEN_PVAR_273 k f dom neut i) = (term190 A K GEN_PVAR_273 k f dom neut i).
Proof. exact (eq_refl (term198 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776307 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (GEN_PVAR_273 : K) : (term204 A K _88612 k f dom neut GEN_PVAR_273) = (term204 A K _88612 k f dom neut GEN_PVAR_273).
Proof. exact (eq_refl (term204 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6776308 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term346 A K _88612 GEN_PVAR_273 k f dom neut i) = (term347 A K _88612 GEN_PVAR_273 k f dom neut i).
Proof. exact (MK_COMB (@lem6776307 A K _88612 k f dom neut GEN_PVAR_273) (@lem6776306 A K GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776309 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term348 A K _88612 GEN_PVAR_273 k f dom neut) = (term349 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6776308 A K _88612 GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776310 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776311 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term340 A K _88612 GEN_PVAR_273 k f dom neut) = (term350 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6776310 K) (@lem6776309 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776312 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term339 A K _88612 GEN_PVAR_273 k f dom neut) = (term340 A K _88612 GEN_PVAR_273 k f dom neut)) = ((term205 A K _88612 GEN_PVAR_273 k f dom neut) = (term350 A K _88612 GEN_PVAR_273 k f dom neut)).
Proof. exact (MK_COMB (@lem6776305 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6776311 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776313 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term205 A K _88612 GEN_PVAR_273 k f dom neut) = (term350 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (EQ_MP (@lem6776312 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6776297 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776314 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term228 A K _88612 k f dom neut) = (term351 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6776313 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776315 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6776316 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term243 A K _88612 k f dom neut) = (term352 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776315 K) (@lem6776314 A K _88612 k f dom neut)). Qed.
Lemma lem6776318 {A B : Type'} (P : type1413 A B) : (term353 A B P) = (term354 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6776319 {K : Type'} (P : type1402 K) : (term355 K P) = (term356 K P).
Proof. exact (@lem6776318 K K P). Qed.
Lemma lem6776320 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term357 A K _88612 k f dom neut) = (term358 A K _88612 k f dom neut).
Proof. exact (@lem6776319 K (term359 A K _88612 k f dom neut)). Qed.
Lemma lem6776321 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term360 A K _88612 k f dom neut GEN_PVAR_273) = (term349 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term360 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6776322 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6776323 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term361 A K _88612 k f dom neut GEN_PVAR_273 i) = (term362 A K _88612 GEN_PVAR_273 k f dom neut i).
Proof. exact (MK_COMB (@lem6776321 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6776322 K i)). Qed.
Lemma lem6776324 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term362 A K _88612 GEN_PVAR_273 k f dom neut i) = (term347 A K _88612 GEN_PVAR_273 k f dom neut i).
Proof. exact (eq_refl (term362 A K _88612 GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776325 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term361 A K _88612 k f dom neut GEN_PVAR_273 i) = (term347 A K _88612 GEN_PVAR_273 k f dom neut i).
Proof. exact (TRANS (@lem6776323 A K _88612 GEN_PVAR_273 k f dom neut i) (@lem6776324 A K _88612 GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776326 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term363 A K _88612 k f dom neut GEN_PVAR_273) = (term349 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (fun_ext (fun i : K => @lem6776325 A K _88612 GEN_PVAR_273 k f dom neut i)). Qed.
Lemma lem6776327 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776328 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term364 A K _88612 k f dom neut GEN_PVAR_273) = (term350 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (MK_COMB (@lem6776327 K) (@lem6776326 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776329 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term365 A K _88612 k f dom neut) = (term351 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6776328 A K _88612 GEN_PVAR_273 k f dom neut)). Qed.
Lemma lem6776330 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6776331 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term357 A K _88612 k f dom neut) = (term352 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776330 K) (@lem6776329 A K _88612 k f dom neut)). Qed.
Lemma lem6776332 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776333 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term366 A K _88612 k f dom neut) = (term367 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776332) (@lem6776331 A K _88612 k f dom neut)). Qed.
Lemma lem6776334 {A K : Type'} (_88612 : type849 A K) (GEN_PVAR_273 : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term360 A K _88612 k f dom neut GEN_PVAR_273) = (term349 A K _88612 GEN_PVAR_273 k f dom neut).
Proof. exact (eq_refl (term360 A K _88612 k f dom neut GEN_PVAR_273)). Qed.
Lemma lem6776335 {K : Type'} (i : K -> K) (GEN_PVAR_273 : K) : (i GEN_PVAR_273) = (i GEN_PVAR_273).
Proof. exact (eq_refl (i GEN_PVAR_273)). Qed.
Lemma lem6776336 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) (GEN_PVAR_273 : K) : (term368 A K _88612 k f dom neut i GEN_PVAR_273) = (term369 A K _88612 k f dom neut i GEN_PVAR_273).
Proof. exact (MK_COMB (@lem6776334 A K _88612 GEN_PVAR_273 k f dom neut) (@lem6776335 K i GEN_PVAR_273)). Qed.
Lemma lem6776337 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) (GEN_PVAR_273 : K) : (term369 A K _88612 k f dom neut i GEN_PVAR_273) = (term370 A K _88612 k f dom neut i GEN_PVAR_273).
Proof. exact (eq_refl (term369 A K _88612 k f dom neut i GEN_PVAR_273)). Qed.
Lemma lem6776338 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) (GEN_PVAR_273 : K) : (term368 A K _88612 k f dom neut i GEN_PVAR_273) = (term370 A K _88612 k f dom neut i GEN_PVAR_273).
Proof. exact (TRANS (@lem6776336 A K _88612 k f dom neut i GEN_PVAR_273) (@lem6776337 A K _88612 k f dom neut i GEN_PVAR_273)). Qed.
Lemma lem6776339 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) : (term371 A K _88612 k f dom neut i) = (term372 A K _88612 k f dom neut i).
Proof. exact (fun_ext (fun GEN_PVAR_273 : K => @lem6776338 A K _88612 k f dom neut i GEN_PVAR_273)). Qed.
Lemma lem6776340 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6776341 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) : (term373 A K _88612 k f dom neut i) = (term374 A K _88612 k f dom neut i).
Proof. exact (MK_COMB (@lem6776340 K) (@lem6776339 A K _88612 k f dom neut i)). Qed.
Lemma lem6776342 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term375 A K _88612 k f dom neut) = (term376 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun i : K -> K => @lem6776341 A K _88612 k f dom neut i)). Qed.
Lemma lem6776343 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6776344 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term358 A K _88612 k f dom neut) = (term377 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776343 K) (@lem6776342 A K _88612 k f dom neut)). Qed.
Lemma lem6776345 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : ((term357 A K _88612 k f dom neut) = (term358 A K _88612 k f dom neut)) = ((term352 A K _88612 k f dom neut) = (term377 A K _88612 k f dom neut)).
Proof. exact (MK_COMB (@lem6776333 A K _88612 k f dom neut) (@lem6776344 A K _88612 k f dom neut)). Qed.
Lemma lem6776346 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term352 A K _88612 k f dom neut) = (term377 A K _88612 k f dom neut).
Proof. exact (EQ_MP (@lem6776345 A K _88612 k f dom neut) (@lem6776320 A K _88612 k f dom neut)). Qed.
Lemma lem6776347 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term243 A K _88612 k f dom neut) = (term377 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6776316 A K _88612 k f dom neut) (@lem6776346 A K _88612 k f dom neut)). Qed.
Lemma lem6776348 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term250 A K _88612 k f dom) = (term378 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6776347 A K _88612 k f dom neut)). Qed.
Lemma lem6776349 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6776350 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term265 A K _88612 k f dom) = (term379 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6776349 A) (@lem6776348 A K _88612 k f dom)). Qed.
Lemma lem6776352 {A B : Type'} (P : type1413 A B) : (term353 A B P) = (term354 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6776353 {A K : Type'} (P : type1373 A K) : (term380 A K P) = (term381 A K P).
Proof. exact (@lem6776352 A (K -> K) P). Qed.
Lemma lem6776354 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term382 A K _88612 k f dom) = (term383 A K _88612 k f dom).
Proof. exact (@lem6776353 A K (term384 A K _88612 k f dom)). Qed.
Lemma lem6776355 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term385 A K _88612 k f dom neut) = (term376 A K _88612 k f dom neut).
Proof. exact (eq_refl (term385 A K _88612 k f dom neut)). Qed.
Lemma lem6776356 {K : Type'} (i : K -> K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6776357 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) : (term386 A K _88612 k f dom neut i) = (term387 A K _88612 k f dom neut i).
Proof. exact (MK_COMB (@lem6776355 A K _88612 k f dom neut) (@lem6776356 K i)). Qed.
Lemma lem6776358 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) : (term387 A K _88612 k f dom neut i) = (term374 A K _88612 k f dom neut i).
Proof. exact (eq_refl (term387 A K _88612 k f dom neut i)). Qed.
Lemma lem6776359 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K -> K) : (term386 A K _88612 k f dom neut i) = (term374 A K _88612 k f dom neut i).
Proof. exact (TRANS (@lem6776357 A K _88612 k f dom neut i) (@lem6776358 A K _88612 k f dom neut i)). Qed.
Lemma lem6776360 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term388 A K _88612 k f dom neut) = (term376 A K _88612 k f dom neut).
Proof. exact (fun_ext (fun i : K -> K => @lem6776359 A K _88612 k f dom neut i)). Qed.
Lemma lem6776361 {K : Type'} : (@ex (K -> K)) = (@ex (K -> K)).
Proof. exact (eq_refl (@ex (K -> K))). Qed.
Lemma lem6776362 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term389 A K _88612 k f dom neut) = (term377 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776361 K) (@lem6776360 A K _88612 k f dom neut)). Qed.
Lemma lem6776363 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term390 A K _88612 k f dom) = (term378 A K _88612 k f dom).
Proof. exact (fun_ext (fun neut : A => @lem6776362 A K _88612 k f dom neut)). Qed.
Lemma lem6776364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6776365 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term382 A K _88612 k f dom) = (term379 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6776364 A) (@lem6776363 A K _88612 k f dom)). Qed.
Lemma lem6776366 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776367 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term391 A K _88612 k f dom) = (term392 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6776366) (@lem6776365 A K _88612 k f dom)). Qed.
Lemma lem6776368 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term385 A K _88612 k f dom neut) = (term376 A K _88612 k f dom neut).
Proof. exact (eq_refl (term385 A K _88612 k f dom neut)). Qed.
Lemma lem6776369 {A K : Type'} (i : type1411 A K) (neut : A) : (i neut) = (i neut).
Proof. exact (eq_refl (i neut)). Qed.
Lemma lem6776370 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) (neut : A) : (term393 A K _88612 k f dom i neut) = (term394 A K _88612 k f dom i neut).
Proof. exact (MK_COMB (@lem6776368 A K _88612 k f dom neut) (@lem6776369 A K i neut)). Qed.
Lemma lem6776371 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) (neut : A) : (term394 A K _88612 k f dom i neut) = (term395 A K _88612 k f dom i neut).
Proof. exact (eq_refl (term394 A K _88612 k f dom i neut)). Qed.
Lemma lem6776372 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) (neut : A) : (term393 A K _88612 k f dom i neut) = (term395 A K _88612 k f dom i neut).
Proof. exact (TRANS (@lem6776370 A K _88612 k f dom i neut) (@lem6776371 A K _88612 k f dom i neut)). Qed.
Lemma lem6776373 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) : (term396 A K _88612 k f dom i) = (term397 A K _88612 k f dom i).
Proof. exact (fun_ext (fun neut : A => @lem6776372 A K _88612 k f dom i neut)). Qed.
Lemma lem6776374 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem6776375 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) : (term398 A K _88612 k f dom i) = (term399 A K _88612 k f dom i).
Proof. exact (MK_COMB (@lem6776374 A) (@lem6776373 A K _88612 k f dom i)). Qed.
Lemma lem6776376 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term400 A K _88612 k f dom) = (term401 A K _88612 k f dom).
Proof. exact (fun_ext (fun i : type1411 A K => @lem6776375 A K _88612 k f dom i)). Qed.
Lemma lem6776377 {A K : Type'} : (@ex (A -> K -> K)) = (@ex (A -> K -> K)).
Proof. exact (eq_refl (@ex (A -> K -> K))). Qed.
Lemma lem6776378 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term383 A K _88612 k f dom) = (term402 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6776377 A K) (@lem6776376 A K _88612 k f dom)). Qed.
Lemma lem6776379 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : ((term382 A K _88612 k f dom) = (term383 A K _88612 k f dom)) = ((term379 A K _88612 k f dom) = (term402 A K _88612 k f dom)).
Proof. exact (MK_COMB (@lem6776367 A K _88612 k f dom) (@lem6776378 A K _88612 k f dom)). Qed.
Lemma lem6776380 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term379 A K _88612 k f dom) = (term402 A K _88612 k f dom).
Proof. exact (EQ_MP (@lem6776379 A K _88612 k f dom) (@lem6776354 A K _88612 k f dom)). Qed.
Lemma lem6776381 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term265 A K _88612 k f dom) = (term402 A K _88612 k f dom).
Proof. exact (TRANS (@lem6776350 A K _88612 k f dom) (@lem6776380 A K _88612 k f dom)). Qed.
Lemma lem6776382 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term274 A K _88612 k f) = (term403 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6776381 A K _88612 k f dom)). Qed.
Lemma lem6776383 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6776384 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term289 A K _88612 k f) = (term404 A K _88612 k f).
Proof. exact (MK_COMB (@lem6776383 A) (@lem6776382 A K _88612 k f)). Qed.
Lemma lem6776386 {A B : Type'} (P : type1413 A B) : (term353 A B P) = (term354 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6776387 {A K : Type'} (P : type612 A K) : (term405 A K P) = (term406 A K P).
Proof. exact (@lem6776386 (A -> Prop) (type1411 A K) P). Qed.
Lemma lem6776388 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term407 A K _88612 k f) = (term408 A K _88612 k f).
Proof. exact (@lem6776387 A K (term409 A K _88612 k f)). Qed.
Lemma lem6776389 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term410 A K _88612 k f dom) = (term401 A K _88612 k f dom).
Proof. exact (eq_refl (term410 A K _88612 k f dom)). Qed.
Lemma lem6776390 {A K : Type'} (i : type1411 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6776391 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) : (term411 A K _88612 k f dom i) = (term412 A K _88612 k f dom i).
Proof. exact (MK_COMB (@lem6776389 A K _88612 k f dom) (@lem6776390 A K i)). Qed.
Lemma lem6776392 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) : (term412 A K _88612 k f dom i) = (term399 A K _88612 k f dom i).
Proof. exact (eq_refl (term412 A K _88612 k f dom i)). Qed.
Lemma lem6776393 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (i : type1411 A K) : (term411 A K _88612 k f dom i) = (term399 A K _88612 k f dom i).
Proof. exact (TRANS (@lem6776391 A K _88612 k f dom i) (@lem6776392 A K _88612 k f dom i)). Qed.
Lemma lem6776394 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term413 A K _88612 k f dom) = (term401 A K _88612 k f dom).
Proof. exact (fun_ext (fun i : type1411 A K => @lem6776393 A K _88612 k f dom i)). Qed.
Lemma lem6776395 {A K : Type'} : (@ex (A -> K -> K)) = (@ex (A -> K -> K)).
Proof. exact (eq_refl (@ex (A -> K -> K))). Qed.
Lemma lem6776396 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term414 A K _88612 k f dom) = (term402 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6776395 A K) (@lem6776394 A K _88612 k f dom)). Qed.
Lemma lem6776397 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term415 A K _88612 k f) = (term403 A K _88612 k f).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6776396 A K _88612 k f dom)). Qed.
Lemma lem6776398 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6776399 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term407 A K _88612 k f) = (term404 A K _88612 k f).
Proof. exact (MK_COMB (@lem6776398 A) (@lem6776397 A K _88612 k f)). Qed.
Lemma lem6776400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776401 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term416 A K _88612 k f) = (term417 A K _88612 k f).
Proof. exact (MK_COMB (@lem6776400) (@lem6776399 A K _88612 k f)). Qed.
Lemma lem6776402 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term410 A K _88612 k f dom) = (term401 A K _88612 k f dom).
Proof. exact (eq_refl (term410 A K _88612 k f dom)). Qed.
Lemma lem6776403 {A K : Type'} (i : type668 A K) (dom : A -> Prop) : (i dom) = (i dom).
Proof. exact (eq_refl (i dom)). Qed.
Lemma lem6776404 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) (dom : A -> Prop) : (term418 A K _88612 k f i dom) = (term419 A K _88612 k f i dom).
Proof. exact (MK_COMB (@lem6776402 A K _88612 k f dom) (@lem6776403 A K i dom)). Qed.
Lemma lem6776405 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) (dom : A -> Prop) : (term419 A K _88612 k f i dom) = (term420 A K _88612 k f i dom).
Proof. exact (eq_refl (term419 A K _88612 k f i dom)). Qed.
Lemma lem6776406 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) (dom : A -> Prop) : (term418 A K _88612 k f i dom) = (term420 A K _88612 k f i dom).
Proof. exact (TRANS (@lem6776404 A K _88612 k f i dom) (@lem6776405 A K _88612 k f i dom)). Qed.
Lemma lem6776407 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) : (term421 A K _88612 k f i) = (term422 A K _88612 k f i).
Proof. exact (fun_ext (fun dom : A -> Prop => @lem6776406 A K _88612 k f i dom)). Qed.
Lemma lem6776408 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem6776409 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) : (term423 A K _88612 k f i) = (term424 A K _88612 k f i).
Proof. exact (MK_COMB (@lem6776408 A) (@lem6776407 A K _88612 k f i)). Qed.
Lemma lem6776410 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term425 A K _88612 k f) = (term426 A K _88612 k f).
Proof. exact (fun_ext (fun i : type668 A K => @lem6776409 A K _88612 k f i)). Qed.
Lemma lem6776411 {A K : Type'} : (@ex ((A -> Prop) -> A -> K -> K)) = (@ex ((A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776412 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term408 A K _88612 k f) = (term427 A K _88612 k f).
Proof. exact (MK_COMB (@lem6776411 A K) (@lem6776410 A K _88612 k f)). Qed.
Lemma lem6776413 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : ((term407 A K _88612 k f) = (term408 A K _88612 k f)) = ((term404 A K _88612 k f) = (term427 A K _88612 k f)).
Proof. exact (MK_COMB (@lem6776401 A K _88612 k f) (@lem6776412 A K _88612 k f)). Qed.
Lemma lem6776414 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term404 A K _88612 k f) = (term427 A K _88612 k f).
Proof. exact (EQ_MP (@lem6776413 A K _88612 k f) (@lem6776388 A K _88612 k f)). Qed.
Lemma lem6776415 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term289 A K _88612 k f) = (term427 A K _88612 k f).
Proof. exact (TRANS (@lem6776384 A K _88612 k f) (@lem6776414 A K _88612 k f)). Qed.
Lemma lem6776416 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term298 A K _88612 k) = (term428 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6776415 A K _88612 k f)). Qed.
Lemma lem6776417 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6776418 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term313 A K _88612 k) = (term429 A K _88612 k).
Proof. exact (MK_COMB (@lem6776417 A K) (@lem6776416 A K _88612 k)). Qed.
Lemma lem6776420 {A B : Type'} (P : type1413 A B) : (term353 A B P) = (term354 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6776421 {A K : Type'} (P : type770 A K) : (term430 A K P) = (term431 A K P).
Proof. exact (@lem6776420 (K -> A) (type668 A K) P). Qed.
Lemma lem6776422 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term432 A K _88612 k) = (term433 A K _88612 k).
Proof. exact (@lem6776421 A K (term434 A K _88612 k)). Qed.
Lemma lem6776423 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term435 A K _88612 k f) = (term426 A K _88612 k f).
Proof. exact (eq_refl (term435 A K _88612 k f)). Qed.
Lemma lem6776424 {A K : Type'} (i : type668 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6776425 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) : (term436 A K _88612 k f i) = (term437 A K _88612 k f i).
Proof. exact (MK_COMB (@lem6776423 A K _88612 k f) (@lem6776424 A K i)). Qed.
Lemma lem6776426 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) : (term437 A K _88612 k f i) = (term424 A K _88612 k f i).
Proof. exact (eq_refl (term437 A K _88612 k f i)). Qed.
Lemma lem6776427 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (i : type668 A K) : (term436 A K _88612 k f i) = (term424 A K _88612 k f i).
Proof. exact (TRANS (@lem6776425 A K _88612 k f i) (@lem6776426 A K _88612 k f i)). Qed.
Lemma lem6776428 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term438 A K _88612 k f) = (term426 A K _88612 k f).
Proof. exact (fun_ext (fun i : type668 A K => @lem6776427 A K _88612 k f i)). Qed.
Lemma lem6776429 {A K : Type'} : (@ex ((A -> Prop) -> A -> K -> K)) = (@ex ((A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776430 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term439 A K _88612 k f) = (term427 A K _88612 k f).
Proof. exact (MK_COMB (@lem6776429 A K) (@lem6776428 A K _88612 k f)). Qed.
Lemma lem6776431 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term440 A K _88612 k) = (term428 A K _88612 k).
Proof. exact (fun_ext (fun f : K -> A => @lem6776430 A K _88612 k f)). Qed.
Lemma lem6776432 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6776433 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term432 A K _88612 k) = (term429 A K _88612 k).
Proof. exact (MK_COMB (@lem6776432 A K) (@lem6776431 A K _88612 k)). Qed.
Lemma lem6776434 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776435 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term441 A K _88612 k) = (term442 A K _88612 k).
Proof. exact (MK_COMB (@lem6776434) (@lem6776433 A K _88612 k)). Qed.
Lemma lem6776436 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (term435 A K _88612 k f) = (term426 A K _88612 k f).
Proof. exact (eq_refl (term435 A K _88612 k f)). Qed.
Lemma lem6776437 {A K : Type'} (i : type780 A K) (f : K -> A) : (i f) = (i f).
Proof. exact (eq_refl (i f)). Qed.
Lemma lem6776438 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) (f : K -> A) : (term443 A K _88612 k i f) = (term444 A K _88612 k i f).
Proof. exact (MK_COMB (@lem6776436 A K _88612 k f) (@lem6776437 A K i f)). Qed.
Lemma lem6776439 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) (f : K -> A) : (term444 A K _88612 k i f) = (term445 A K _88612 k i f).
Proof. exact (eq_refl (term444 A K _88612 k i f)). Qed.
Lemma lem6776440 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) (f : K -> A) : (term443 A K _88612 k i f) = (term445 A K _88612 k i f).
Proof. exact (TRANS (@lem6776438 A K _88612 k i f) (@lem6776439 A K _88612 k i f)). Qed.
Lemma lem6776441 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) : (term446 A K _88612 k i) = (term447 A K _88612 k i).
Proof. exact (fun_ext (fun f : K -> A => @lem6776440 A K _88612 k i f)). Qed.
Lemma lem6776442 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem6776443 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) : (term448 A K _88612 k i) = (term449 A K _88612 k i).
Proof. exact (MK_COMB (@lem6776442 A K) (@lem6776441 A K _88612 k i)). Qed.
Lemma lem6776444 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term450 A K _88612 k) = (term451 A K _88612 k).
Proof. exact (fun_ext (fun i : type780 A K => @lem6776443 A K _88612 k i)). Qed.
Lemma lem6776445 {A K : Type'} : (@ex ((K -> A) -> (A -> Prop) -> A -> K -> K)) = (@ex ((K -> A) -> (A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> (A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776446 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term433 A K _88612 k) = (term452 A K _88612 k).
Proof. exact (MK_COMB (@lem6776445 A K) (@lem6776444 A K _88612 k)). Qed.
Lemma lem6776447 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : ((term432 A K _88612 k) = (term433 A K _88612 k)) = ((term429 A K _88612 k) = (term452 A K _88612 k)).
Proof. exact (MK_COMB (@lem6776435 A K _88612 k) (@lem6776446 A K _88612 k)). Qed.
Lemma lem6776448 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term429 A K _88612 k) = (term452 A K _88612 k).
Proof. exact (EQ_MP (@lem6776447 A K _88612 k) (@lem6776422 A K _88612 k)). Qed.
Lemma lem6776449 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term313 A K _88612 k) = (term452 A K _88612 k).
Proof. exact (TRANS (@lem6776418 A K _88612 k) (@lem6776448 A K _88612 k)). Qed.
Lemma lem6776450 {A K : Type'} (_88612 : type849 A K) : (term320 A K _88612) = (term453 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776449 A K _88612 k)). Qed.
Lemma lem6776451 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776452 {A K : Type'} (_88612 : type849 A K) : (term335 A K _88612) = (term454 A K _88612).
Proof. exact (MK_COMB (@lem6776451 K) (@lem6776450 A K _88612)). Qed.
Lemma lem6776454 {A B : Type'} (P : type1413 A B) : (term353 A B P) = (term354 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem6776455 {A K : Type'} (P : type826 A K) : (term455 A K P) = (term456 A K P).
Proof. exact (@lem6776454 (K -> Prop) (type780 A K) P). Qed.
Lemma lem6776456 {A K : Type'} (_88612 : type849 A K) : (term457 A K _88612) = (term458 A K _88612).
Proof. exact (@lem6776455 A K (term459 A K _88612)). Qed.
Lemma lem6776457 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term460 A K _88612 k) = (term451 A K _88612 k).
Proof. exact (eq_refl (term460 A K _88612 k)). Qed.
Lemma lem6776458 {A K : Type'} (i : type780 A K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6776459 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) : (term461 A K _88612 k i) = (term462 A K _88612 k i).
Proof. exact (MK_COMB (@lem6776457 A K _88612 k) (@lem6776458 A K i)). Qed.
Lemma lem6776460 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) : (term462 A K _88612 k i) = (term449 A K _88612 k i).
Proof. exact (eq_refl (term462 A K _88612 k i)). Qed.
Lemma lem6776461 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (i : type780 A K) : (term461 A K _88612 k i) = (term449 A K _88612 k i).
Proof. exact (TRANS (@lem6776459 A K _88612 k i) (@lem6776460 A K _88612 k i)). Qed.
Lemma lem6776462 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term463 A K _88612 k) = (term451 A K _88612 k).
Proof. exact (fun_ext (fun i : type780 A K => @lem6776461 A K _88612 k i)). Qed.
Lemma lem6776463 {A K : Type'} : (@ex ((K -> A) -> (A -> Prop) -> A -> K -> K)) = (@ex ((K -> A) -> (A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> A) -> (A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776464 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term464 A K _88612 k) = (term452 A K _88612 k).
Proof. exact (MK_COMB (@lem6776463 A K) (@lem6776462 A K _88612 k)). Qed.
Lemma lem6776465 {A K : Type'} (_88612 : type849 A K) : (term465 A K _88612) = (term453 A K _88612).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776464 A K _88612 k)). Qed.
Lemma lem6776466 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776467 {A K : Type'} (_88612 : type849 A K) : (term457 A K _88612) = (term454 A K _88612).
Proof. exact (MK_COMB (@lem6776466 K) (@lem6776465 A K _88612)). Qed.
Lemma lem6776468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776469 {A K : Type'} (_88612 : type849 A K) : (term466 A K _88612) = (term467 A K _88612).
Proof. exact (MK_COMB (@lem6776468) (@lem6776467 A K _88612)). Qed.
Lemma lem6776470 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (term460 A K _88612 k) = (term451 A K _88612 k).
Proof. exact (eq_refl (term460 A K _88612 k)). Qed.
Lemma lem6776471 {A K : Type'} (i : type848 A K) (k : K -> Prop) : (i k) = (i k).
Proof. exact (eq_refl (i k)). Qed.
Lemma lem6776472 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) (k : K -> Prop) : (term468 A K _88612 i k) = (term469 A K _88612 i k).
Proof. exact (MK_COMB (@lem6776470 A K _88612 k) (@lem6776471 A K i k)). Qed.
Lemma lem6776473 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) (k : K -> Prop) : (term469 A K _88612 i k) = (term470 A K _88612 i k).
Proof. exact (eq_refl (term469 A K _88612 i k)). Qed.
Lemma lem6776474 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) (k : K -> Prop) : (term468 A K _88612 i k) = (term470 A K _88612 i k).
Proof. exact (TRANS (@lem6776472 A K _88612 i k) (@lem6776473 A K _88612 i k)). Qed.
Lemma lem6776475 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) : (term471 A K _88612 i) = (term472 A K _88612 i).
Proof. exact (fun_ext (fun k : K -> Prop => @lem6776474 A K _88612 i k)). Qed.
Lemma lem6776476 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem6776477 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) : (term473 A K _88612 i) = (term474 A K _88612 i).
Proof. exact (MK_COMB (@lem6776476 K) (@lem6776475 A K _88612 i)). Qed.
Lemma lem6776478 {A K : Type'} (_88612 : type849 A K) : (term475 A K _88612) = (term476 A K _88612).
Proof. exact (fun_ext (fun i : type848 A K => @lem6776477 A K _88612 i)). Qed.
Lemma lem6776479 {A K : Type'} : (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K)) = (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776480 {A K : Type'} (_88612 : type849 A K) : (term458 A K _88612) = (term477 A K _88612).
Proof. exact (MK_COMB (@lem6776479 A K) (@lem6776478 A K _88612)). Qed.
Lemma lem6776481 {A K : Type'} (_88612 : type849 A K) : ((term457 A K _88612) = (term458 A K _88612)) = ((term454 A K _88612) = (term477 A K _88612)).
Proof. exact (MK_COMB (@lem6776469 A K _88612) (@lem6776480 A K _88612)). Qed.
Lemma lem6776482 {A K : Type'} (_88612 : type849 A K) : (term454 A K _88612) = (term477 A K _88612).
Proof. exact (EQ_MP (@lem6776481 A K _88612) (@lem6776456 A K _88612)). Qed.
Lemma lem6776483 {A K : Type'} (_88612 : type849 A K) : (term335 A K _88612) = (term477 A K _88612).
Proof. exact (TRANS (@lem6776452 A K _88612) (@lem6776482 A K _88612)). Qed.
Lemma lem6776484 {A K : Type'} (_88612 : type849 A K) : (term332 A K _88612) = (term332 A K _88612).
Proof. exact (eq_refl (term332 A K _88612)). Qed.
Lemma lem6776485 {A K : Type'} (_88612 : type849 A K) : (term336 A K _88612) = (term478 A K _88612).
Proof. exact (MK_COMB (@lem6776484 A K _88612) (@lem6776483 A K _88612)). Qed.
Lemma lem6776487 {A : Type'} (P : Prop) (Q : A -> Prop) : (term479 A P Q) = (term480 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem6776488 {A K : Type'} (P : Prop) (Q : type218 A K) : (term481 A K P Q) = (term482 A K P Q).
Proof. exact (@lem6776487 (type848 A K) P Q). Qed.
Lemma lem6776489 {A K : Type'} (_88612 : type849 A K) : (term483 A K _88612) = (term484 A K _88612).
Proof. exact (@lem6776488 A K (term330 A K _88612) (term476 A K _88612)). Qed.
Lemma lem6776490 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) : (term485 A K _88612 i) = (term474 A K _88612 i).
Proof. exact (eq_refl (term485 A K _88612 i)). Qed.
Lemma lem6776491 {A K : Type'} (_88612 : type849 A K) : (term486 A K _88612) = (term476 A K _88612).
Proof. exact (fun_ext (fun i : type848 A K => @lem6776490 A K _88612 i)). Qed.
Lemma lem6776492 {A K : Type'} : (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K)) = (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776493 {A K : Type'} (_88612 : type849 A K) : (term487 A K _88612) = (term477 A K _88612).
Proof. exact (MK_COMB (@lem6776492 A K) (@lem6776491 A K _88612)). Qed.
Lemma lem6776494 {A K : Type'} (_88612 : type849 A K) : (term332 A K _88612) = (term332 A K _88612).
Proof. exact (eq_refl (term332 A K _88612)). Qed.
Lemma lem6776495 {A K : Type'} (_88612 : type849 A K) : (term483 A K _88612) = (term478 A K _88612).
Proof. exact (MK_COMB (@lem6776494 A K _88612) (@lem6776493 A K _88612)). Qed.
Lemma lem6776496 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776497 {A K : Type'} (_88612 : type849 A K) : (term488 A K _88612) = (term489 A K _88612).
Proof. exact (MK_COMB (@lem6776496) (@lem6776495 A K _88612)). Qed.
Lemma lem6776498 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) : (term485 A K _88612 i) = (term474 A K _88612 i).
Proof. exact (eq_refl (term485 A K _88612 i)). Qed.
Lemma lem6776499 {A K : Type'} (_88612 : type849 A K) : (term332 A K _88612) = (term332 A K _88612).
Proof. exact (eq_refl (term332 A K _88612)). Qed.
Lemma lem6776500 {A K : Type'} (_88612 : type849 A K) (i : type848 A K) : (term490 A K _88612 i) = (term491 A K _88612 i).
Proof. exact (MK_COMB (@lem6776499 A K _88612) (@lem6776498 A K _88612 i)). Qed.
Lemma lem6776501 {A K : Type'} (_88612 : type849 A K) : (term492 A K _88612) = (term493 A K _88612).
Proof. exact (fun_ext (fun i : type848 A K => @lem6776500 A K _88612 i)). Qed.
Lemma lem6776502 {A K : Type'} : (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K)) = (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K)).
Proof. exact (eq_refl (@ex ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> K))). Qed.
Lemma lem6776503 {A K : Type'} (_88612 : type849 A K) : (term484 A K _88612) = (term494 A K _88612).
Proof. exact (MK_COMB (@lem6776502 A K) (@lem6776501 A K _88612)). Qed.
Lemma lem6776504 {A K : Type'} (_88612 : type849 A K) : ((term483 A K _88612) = (term484 A K _88612)) = ((term478 A K _88612) = (term494 A K _88612)).
Proof. exact (MK_COMB (@lem6776497 A K _88612) (@lem6776503 A K _88612)). Qed.
Lemma lem6776505 {A K : Type'} (_88612 : type849 A K) : (term478 A K _88612) = (term494 A K _88612).
Proof. exact (EQ_MP (@lem6776504 A K _88612) (@lem6776489 A K _88612)). Qed.
Lemma lem6776506 {A K : Type'} (_88612 : type849 A K) : (term336 A K _88612) = (term494 A K _88612).
Proof. exact (TRANS (@lem6776485 A K _88612) (@lem6776505 A K _88612)). Qed.
Lemma lem6776507 {A K : Type'} (_88612 : type849 A K) : (term222 A K _88612) = (term494 A K _88612).
Proof. exact (TRANS (@lem6776293 A K _88612) (@lem6776506 A K _88612)). Qed.
Lemma lem6776508 {A K : Type'} (_88612 : type849 A K) : (term185 A K _88612) = (term494 A K _88612).
Proof. exact (TRANS (@lem6775526 A K _88612) (@lem6776507 A K _88612)). Qed.
Lemma lem6776509 {A K : Type'} (_88612 : type849 A K) (h1 : term185 A K _88612) : term494 A K _88612.
Proof. exact (EQ_MP (@lem6776508 A K _88612) (@lem6775476 A K _88612 h1)). Qed.
Lemma lem6776515 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) : term85 A K _88612 k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6776526 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term89 K k ltle j i) = (term495 K k ltle j i).
Proof. exact (@lem17265 (@IN K j k) (term496 K ltle j i)). Qed.
Lemma lem6776527 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term90 K k ltle i) = (term497 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6776526 K k ltle j i)). Qed.
Lemma lem6776528 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6776581 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term21 K k ltle i) = (term498 K k ltle i).
Proof. exact (MK_COMB (@lem6776528 K) (@lem6776527 K k ltle i)). Qed.
Lemma lem6776582 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term498 K k ltle i.
Proof. exact (EQ_MP (@lem6776581 K k ltle i) (@lem6775478 K k ltle i h1)). Qed.
Lemma lem6776592 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term499 K ltle j i) = (term500 K ltle j i).
Proof. exact (@lem17160 (ltle i j) (ltle j i)). Qed.
Lemma lem6776594 {K : Type'} (i : K) (j : K) : (term501 K i j) = (term501 K i j).
Proof. exact (eq_refl (term501 K i j)). Qed.
Lemma lem6776595 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term502 K ltle j i) = (term503 K ltle j i).
Proof. exact (MK_COMB (@lem6776594 K i j) (@lem6776592 K ltle j i)). Qed.
Lemma lem6776596 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term504 K ltle j i) = (term502 K ltle j i).
Proof. exact (@lem17160 (i = j) (term505 K ltle j i)). Qed.
Lemma lem6776597 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term504 K ltle j i) = (term503 K ltle j i).
Proof. exact (TRANS (@lem6776596 K ltle j i) (@lem6776595 K ltle j i)). Qed.
Lemma lem6776599 {K : Type'} (j : K) (k : K -> Prop) : (term506 K j k) = (term506 K j k).
Proof. exact (eq_refl (term506 K j k)). Qed.
Lemma lem6776600 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term507 K k ltle j i) = (term508 K k ltle j i).
Proof. exact (MK_COMB (@lem6776599 K j k) (@lem6776597 K ltle j i)). Qed.
Lemma lem6776601 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term509 K k ltle j i) = (term507 K k ltle j i).
Proof. exact (@lem17362 (@IN K j k) (term510 K ltle j i)). Qed.
Lemma lem6776602 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term509 K k ltle j i) = (term508 K k ltle j i).
Proof. exact (TRANS (@lem6776601 K k ltle j i) (@lem6776600 K k ltle j i)). Qed.
Lemma lem6776603 {K : Type'} (P : K -> Prop) : (term511 K P) = (term512 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem6776604 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term513 K k ltle i) = (term514 K k ltle i).
Proof. exact (@lem6776603 K (term79 K k ltle i)). Qed.
Lemma lem6776605 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term515 K k ltle i j) = (term78 K k ltle j i).
Proof. exact (eq_refl (term515 K k ltle i j)). Qed.
Lemma lem6776606 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6776607 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term516 K k ltle i j) = (term509 K k ltle j i).
Proof. exact (MK_COMB (@lem6776606) (@lem6776605 K k ltle j i)). Qed.
Lemma lem6776608 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term516 K k ltle i j) = (term508 K k ltle j i).
Proof. exact (TRANS (@lem6776607 K k ltle j i) (@lem6776602 K k ltle j i)). Qed.
Lemma lem6776609 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term517 K k ltle i) = (term518 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6776608 K k ltle j i)). Qed.
Lemma lem6776610 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776611 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term514 K k ltle i) = (term519 K k ltle i).
Proof. exact (MK_COMB (@lem6776610 K) (@lem6776609 K k ltle i)). Qed.
Lemma lem6776612 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term513 K k ltle i) = (term519 K k ltle i).
Proof. exact (TRANS (@lem6776604 K k ltle i) (@lem6776611 K k ltle i)). Qed.
Lemma lem6776627 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term520 A K ltle k f dom neut j i) = (term521 A K ltle k f dom neut j i).
Proof. exact (@lem17362 (term522 A K ltle i k f j dom neut) (j = i)). Qed.
Lemma lem6776628 {K : Type'} (P : K -> Prop) : (term511 K P) = (term512 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem6776629 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term523 A K ltle k f dom neut i) = (term524 A K ltle k f dom neut i).
Proof. exact (@lem6776628 K (term76 A K ltle k f dom neut i)). Qed.
Lemma lem6776630 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term525 A K ltle k f dom neut i j) = (term75 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term525 A K ltle k f dom neut i j)). Qed.
Lemma lem6776631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6776632 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term526 A K ltle k f dom neut i j) = (term520 A K ltle k f dom neut j i).
Proof. exact (MK_COMB (@lem6776631) (@lem6776630 A K ltle k f dom neut j i)). Qed.
Lemma lem6776633 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term526 A K ltle k f dom neut i j) = (term521 A K ltle k f dom neut j i).
Proof. exact (TRANS (@lem6776632 A K ltle k f dom neut j i) (@lem6776627 A K ltle k f dom neut j i)). Qed.
Lemma lem6776634 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term527 A K ltle k f dom neut i) = (term528 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6776633 A K ltle k f dom neut j i)). Qed.
Lemma lem6776635 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776636 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term524 A K ltle k f dom neut i) = (term529 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776635 K) (@lem6776634 A K ltle k f dom neut i)). Qed.
Lemma lem6776637 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term523 A K ltle k f dom neut i) = (term529 A K ltle k f dom neut i).
Proof. exact (TRANS (@lem6776629 A K ltle k f dom neut i) (@lem6776636 A K ltle k f dom neut i)). Qed.
Lemma lem6776638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6776639 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term530 K k ltle i) = (term531 K k ltle i).
Proof. exact (MK_COMB (@lem6776638) (@lem6776612 K k ltle i)). Qed.
Lemma lem6776640 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term532 A K ltle k f dom neut i) = (term533 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776639 K k ltle i) (@lem6776637 A K ltle k f dom neut i)). Qed.
Lemma lem6776641 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term534 A K ltle k f dom neut i) = (term532 A K ltle k f dom neut i).
Proof. exact (@lem17045 (term80 K k ltle i) (term77 A K ltle k f dom neut i)). Qed.
Lemma lem6776642 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term534 A K ltle k f dom neut i) = (term533 A K ltle k f dom neut i).
Proof. exact (TRANS (@lem6776641 A K ltle k f dom neut i) (@lem6776640 A K ltle k f dom neut i)). Qed.
Lemma lem6776644 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term535 A K _88612 k f dom neut) = (term535 A K _88612 k f dom neut).
Proof. exact (eq_refl (term535 A K _88612 k f dom neut)). Qed.
Lemma lem6776645 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term536 A K _88612 ltle k f dom neut i) = (term537 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776644 A K _88612 k f dom neut) (@lem6776642 A K ltle k f dom neut i)). Qed.
Lemma lem6776646 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term193 A K _88612 ltle k f dom neut i) = (term536 A K _88612 ltle k f dom neut i).
Proof. exact (@lem17045 (term85 A K _88612 k f dom neut) (term82 A K ltle k f dom neut i)). Qed.
Lemma lem6776647 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term193 A K _88612 ltle k f dom neut i) = (term537 A K _88612 ltle k f dom neut i).
Proof. exact (TRANS (@lem6776646 A K _88612 ltle k f dom neut i) (@lem6776645 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776746 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term538 A P Q) = (term539 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem6776747 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term538 K P Q) = (term539 K P Q).
Proof. exact (@lem6776746 K P Q). Qed.
Lemma lem6776748 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term540 A K ltle k f dom neut i) = (term541 A K ltle k f dom neut i).
Proof. exact (@lem6776747 K (term518 K k ltle i) (term528 A K ltle k f dom neut i)). Qed.
Lemma lem6776749 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term542 K k ltle i j) = (term508 K k ltle j i).
Proof. exact (eq_refl (term542 K k ltle i j)). Qed.
Lemma lem6776750 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term543 K k ltle i) = (term518 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6776749 K k ltle j i)). Qed.
Lemma lem6776751 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776752 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term544 K k ltle i) = (term519 K k ltle i).
Proof. exact (MK_COMB (@lem6776751 K) (@lem6776750 K k ltle i)). Qed.
Lemma lem6776753 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6776754 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term545 K k ltle i) = (term531 K k ltle i).
Proof. exact (MK_COMB (@lem6776753) (@lem6776752 K k ltle i)). Qed.
Lemma lem6776755 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term546 A K ltle k f dom neut i j) = (term521 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term546 A K ltle k f dom neut i j)). Qed.
Lemma lem6776756 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term547 A K ltle k f dom neut i) = (term528 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6776755 A K ltle k f dom neut j i)). Qed.
Lemma lem6776757 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776758 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term548 A K ltle k f dom neut i) = (term529 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776757 K) (@lem6776756 A K ltle k f dom neut i)). Qed.
Lemma lem6776759 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term540 A K ltle k f dom neut i) = (term533 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776754 K k ltle i) (@lem6776758 A K ltle k f dom neut i)). Qed.
Lemma lem6776760 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776761 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term549 A K ltle k f dom neut i) = (term550 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776760) (@lem6776759 A K ltle k f dom neut i)). Qed.
Lemma lem6776762 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term542 K k ltle i j) = (term508 K k ltle j i).
Proof. exact (eq_refl (term542 K k ltle i j)). Qed.
Lemma lem6776763 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6776764 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term551 K k ltle i j) = (term552 K k ltle j i).
Proof. exact (MK_COMB (@lem6776763) (@lem6776762 K k ltle j i)). Qed.
Lemma lem6776765 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term546 A K ltle k f dom neut i j) = (term521 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term546 A K ltle k f dom neut i j)). Qed.
Lemma lem6776766 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term553 A K ltle k f dom neut i j) = (term554 A K ltle k f dom neut j i).
Proof. exact (MK_COMB (@lem6776764 K k ltle j i) (@lem6776765 A K ltle k f dom neut j i)). Qed.
Lemma lem6776767 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term555 A K ltle k f dom neut i) = (term556 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6776766 A K ltle k f dom neut j i)). Qed.
Lemma lem6776768 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776769 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term541 A K ltle k f dom neut i) = (term557 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776768 K) (@lem6776767 A K ltle k f dom neut i)). Qed.
Lemma lem6776770 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : ((term540 A K ltle k f dom neut i) = (term541 A K ltle k f dom neut i)) = ((term533 A K ltle k f dom neut i) = (term557 A K ltle k f dom neut i)).
Proof. exact (MK_COMB (@lem6776761 A K ltle k f dom neut i) (@lem6776769 A K ltle k f dom neut i)). Qed.
Lemma lem6776771 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term533 A K ltle k f dom neut i) = (term557 A K ltle k f dom neut i).
Proof. exact (EQ_MP (@lem6776770 A K ltle k f dom neut i) (@lem6776748 A K ltle k f dom neut i)). Qed.
Lemma lem6776772 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term535 A K _88612 k f dom neut) = (term535 A K _88612 k f dom neut).
Proof. exact (eq_refl (term535 A K _88612 k f dom neut)). Qed.
Lemma lem6776773 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term537 A K _88612 ltle k f dom neut i) = (term558 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776772 A K _88612 k f dom neut) (@lem6776771 A K ltle k f dom neut i)). Qed.
Lemma lem6776775 {A : Type'} (P : Prop) (Q : A -> Prop) : (term337 A P Q) = (term338 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem6776776 {K : Type'} (P : Prop) (Q : K -> Prop) : (term337 K P Q) = (term338 K P Q).
Proof. exact (@lem6776775 K P Q). Qed.
Lemma lem6776777 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term559 A K _88612 ltle k f dom neut i) = (term560 A K _88612 ltle k f dom neut i).
Proof. exact (@lem6776776 K (term561 A K _88612 k f dom neut) (term556 A K ltle k f dom neut i)). Qed.
Lemma lem6776778 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term562 A K ltle k f dom neut i j) = (term554 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term562 A K ltle k f dom neut i j)). Qed.
Lemma lem6776779 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term563 A K ltle k f dom neut i) = (term556 A K ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6776778 A K ltle k f dom neut j i)). Qed.
Lemma lem6776780 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776781 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term564 A K ltle k f dom neut i) = (term557 A K ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776780 K) (@lem6776779 A K ltle k f dom neut i)). Qed.
Lemma lem6776782 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term535 A K _88612 k f dom neut) = (term535 A K _88612 k f dom neut).
Proof. exact (eq_refl (term535 A K _88612 k f dom neut)). Qed.
Lemma lem6776783 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term559 A K _88612 ltle k f dom neut i) = (term558 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776782 A K _88612 k f dom neut) (@lem6776781 A K ltle k f dom neut i)). Qed.
Lemma lem6776784 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6776785 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term565 A K _88612 ltle k f dom neut i) = (term566 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776784) (@lem6776783 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776786 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term562 A K ltle k f dom neut i j) = (term554 A K ltle k f dom neut j i).
Proof. exact (eq_refl (term562 A K ltle k f dom neut i j)). Qed.
Lemma lem6776787 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term535 A K _88612 k f dom neut) = (term535 A K _88612 k f dom neut).
Proof. exact (eq_refl (term535 A K _88612 k f dom neut)). Qed.
Lemma lem6776788 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term567 A K _88612 ltle k f dom neut i j) = (term568 A K _88612 ltle k f dom neut j i).
Proof. exact (MK_COMB (@lem6776787 A K _88612 k f dom neut) (@lem6776786 A K ltle k f dom neut j i)). Qed.
Lemma lem6776789 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term569 A K _88612 ltle k f dom neut i) = (term570 A K _88612 ltle k f dom neut i).
Proof. exact (fun_ext (fun j : K => @lem6776788 A K _88612 ltle k f dom neut j i)). Qed.
Lemma lem6776790 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem6776791 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term560 A K _88612 ltle k f dom neut i) = (term571 A K _88612 ltle k f dom neut i).
Proof. exact (MK_COMB (@lem6776790 K) (@lem6776789 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776792 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : ((term559 A K _88612 ltle k f dom neut i) = (term560 A K _88612 ltle k f dom neut i)) = ((term558 A K _88612 ltle k f dom neut i) = (term571 A K _88612 ltle k f dom neut i)).
Proof. exact (MK_COMB (@lem6776785 A K _88612 ltle k f dom neut i) (@lem6776791 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776793 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term558 A K _88612 ltle k f dom neut i) = (term571 A K _88612 ltle k f dom neut i).
Proof. exact (EQ_MP (@lem6776792 A K _88612 ltle k f dom neut i) (@lem6776777 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776795 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term537 A K _88612 ltle k f dom neut i) = (term571 A K _88612 ltle k f dom neut i).
Proof. exact (TRANS (@lem6776773 A K _88612 ltle k f dom neut i) (@lem6776793 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776796 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term193 A K _88612 ltle k f dom neut i) = (term571 A K _88612 ltle k f dom neut i).
Proof. exact (TRANS (@lem6776647 A K _88612 ltle k f dom neut i) (@lem6776795 A K _88612 ltle k f dom neut i)). Qed.
Lemma lem6776797 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term193 A K _88612 ltle k f dom neut i) : term571 A K _88612 ltle k f dom neut i.
Proof. exact (EQ_MP (@lem6776796 A K _88612 ltle k f dom neut i) (@lem6775483 A K _88612 ltle k f dom neut i h1)). Qed.
Lemma lem6776798 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term568 A K _88612 ltle k f dom neut j i) : term568 A K _88612 ltle k f dom neut j i.
Proof. exact (h1). Qed.
Lemma lem6776800 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6776801 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6776812 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776813 {A K : Type'} (f : type849 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) f x).
Proof. exact (@lem6776812 (K -> Prop) (type781 A K) f x). Qed.
Lemma lem6776814 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (_88612 k) = (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k).
Proof. exact (@lem6776813 A K _88612 k). Qed.
Lemma lem6776815 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6776816 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (_88612 k f) = (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k f).
Proof. exact (MK_COMB (@lem6776814 A K _88612 k) (@lem6776815 A K f)). Qed.
Lemma lem6776818 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776819 {A K : Type'} (f : type781 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> (A -> Prop) -> A -> K -> Prop) f x).
Proof. exact (@lem6776818 (K -> A) (type669 A K) f x). Qed.
Lemma lem6776820 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k f) = (term572 A K _88612 k f).
Proof. exact (@lem6776819 A K (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k) f). Qed.
Lemma lem6776821 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (_88612 k f) = (term572 A K _88612 k f).
Proof. exact (TRANS (@lem6776816 A K _88612 k f) (@lem6776820 A K _88612 k f)). Qed.
Lemma lem6776822 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6776823 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (_88612 k f dom) = (term573 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6776821 A K _88612 k f) (@lem6776822 A dom)). Qed.
Lemma lem6776825 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776826 {A K : Type'} (f : type669 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> K -> Prop) f x).
Proof. exact (@lem6776825 (A -> Prop) (type1413 A K) f x). Qed.
Lemma lem6776827 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term573 A K _88612 k f dom) = (term574 A K _88612 k f dom).
Proof. exact (@lem6776826 A K (term572 A K _88612 k f) dom). Qed.
Lemma lem6776828 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (_88612 k f dom) = (term574 A K _88612 k f dom).
Proof. exact (TRANS (@lem6776823 A K _88612 k f dom) (@lem6776827 A K _88612 k f dom)). Qed.
Lemma lem6776829 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6776830 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (_88612 k f dom neut) = (term575 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776828 A K _88612 k f dom) (@lem6776829 A neut)). Qed.
Lemma lem6776832 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776833 {A K : Type'} (f : type1413 A K) (x : A) : (f x) = (@I (A -> K -> Prop) f x).
Proof. exact (@lem6776832 A (K -> Prop) f x). Qed.
Lemma lem6776834 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term575 A K _88612 k f dom neut) = (term576 A K _88612 k f dom neut).
Proof. exact (@lem6776833 A K (term574 A K _88612 k f dom) neut). Qed.
Lemma lem6776836 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (_88612 k f dom neut) = (term576 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6776830 A K _88612 k f dom neut) (@lem6776834 A K _88612 k f dom neut)). Qed.
Lemma lem6776837 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term84 A K _88612 k f dom neut) = (term577 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776801 K) (@lem6776836 A K _88612 k f dom neut)). Qed.
Lemma lem6776839 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776840 {K : Type'} (f : type672 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> K -> Prop) f x).
Proof. exact (@lem6776839 (K -> Prop) (K -> Prop) f x). Qed.
Lemma lem6776841 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term577 A K _88612 k f dom neut) = (term578 A K _88612 k f dom neut).
Proof. exact (@lem6776840 K (@GSPEC K) (term576 A K _88612 k f dom neut)). Qed.
Lemma lem6776842 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term84 A K _88612 k f dom neut) = (term578 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6776837 A K _88612 k f dom neut) (@lem6776841 A K _88612 k f dom neut)). Qed.
Lemma lem6776843 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term85 A K _88612 k f dom neut) = (term579 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6776800 K) (@lem6776842 A K _88612 k f dom neut)). Qed.
Lemma lem6776845 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776846 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem6776845 (K -> Prop) Prop f x). Qed.
Lemma lem6776847 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term579 A K _88612 k f dom neut) = (term580 A K _88612 k f dom neut).
Proof. exact (@lem6776846 K (@FINITE K) (term578 A K _88612 k f dom neut)). Qed.
Lemma lem6776848 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term85 A K _88612 k f dom neut) = (term580 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6776843 A K _88612 k f dom neut) (@lem6776847 A K _88612 k f dom neut)). Qed.
Lemma lem6776850 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6776857 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776858 {K : Type'} (f : type1402 K) (x : K) : (f x) = (@I (K -> K -> Prop) f x).
Proof. exact (@lem6776857 K (K -> Prop) f x). Qed.
Lemma lem6776859 {K : Type'} (ltle : type1402 K) (j : K) : (ltle j) = (@I (K -> K -> Prop) ltle j).
Proof. exact (@lem6776858 K ltle j). Qed.
Lemma lem6776860 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6776861 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (ltle j i) = (@I (K -> K -> Prop) ltle j i).
Proof. exact (MK_COMB (@lem6776859 K ltle j) (@lem6776860 K i)). Qed.
Lemma lem6776863 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776864 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6776863 K Prop f x). Qed.
Lemma lem6776865 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (@I (K -> K -> Prop) ltle j i) = (term581 K ltle j i).
Proof. exact (@lem6776864 K (@I (K -> K -> Prop) ltle j) i). Qed.
Lemma lem6776867 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (ltle j i) = (term581 K ltle j i).
Proof. exact (TRANS (@lem6776861 K ltle j i) (@lem6776865 K ltle j i)). Qed.
Lemma lem6776868 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term582 K ltle j i) = (term583 K ltle j i).
Proof. exact (MK_COMB (@lem6776850) (@lem6776867 K ltle j i)). Qed.
Lemma lem6776875 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776876 {K : Type'} (f : type1402 K) (x : K) : (f x) = (@I (K -> K -> Prop) f x).
Proof. exact (@lem6776875 K (K -> Prop) f x). Qed.
Lemma lem6776877 {K : Type'} (ltle : type1402 K) (i : K) : (ltle i) = (@I (K -> K -> Prop) ltle i).
Proof. exact (@lem6776876 K ltle i). Qed.
Lemma lem6776878 {K : Type'} (j : K) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6776879 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (ltle i j) = (@I (K -> K -> Prop) ltle i j).
Proof. exact (MK_COMB (@lem6776877 K ltle i) (@lem6776878 K j)). Qed.
Lemma lem6776881 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776882 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6776881 K Prop f x). Qed.
Lemma lem6776883 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (@I (K -> K -> Prop) ltle i j) = (term581 K ltle i j).
Proof. exact (@lem6776882 K (@I (K -> K -> Prop) ltle i) j). Qed.
Lemma lem6776885 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (ltle i j) = (term581 K ltle i j).
Proof. exact (TRANS (@lem6776879 K ltle i j) (@lem6776883 K ltle i j)). Qed.
Lemma lem6776886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6776887 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (term584 K ltle i j) = (term585 K ltle i j).
Proof. exact (MK_COMB (@lem6776886) (@lem6776885 K ltle i j)). Qed.
Lemma lem6776888 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term496 K ltle j i) = (term586 K ltle j i).
Proof. exact (MK_COMB (@lem6776887 K ltle i j) (@lem6776868 K ltle j i)). Qed.
Lemma lem6776889 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6776896 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776897 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem6776896 K (type686 K) f x). Qed.
Lemma lem6776898 {K : Type'} (j : K) : (@IN K j) = (@I (K -> (K -> Prop) -> Prop) (@IN K) j).
Proof. exact (@lem6776897 K (@IN K) j). Qed.
Lemma lem6776899 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6776900 {K : Type'} (j : K) (k : K -> Prop) : (@IN K j k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) j k).
Proof. exact (MK_COMB (@lem6776898 K j) (@lem6776899 K k)). Qed.
Lemma lem6776902 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776903 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem6776902 (K -> Prop) Prop f x). Qed.
Lemma lem6776904 {K : Type'} (j : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) j k) = (term587 K j k).
Proof. exact (@lem6776903 K (@I (K -> (K -> Prop) -> Prop) (@IN K) j) k). Qed.
Lemma lem6776906 {K : Type'} (j : K) (k : K -> Prop) : (@IN K j k) = (term587 K j k).
Proof. exact (TRANS (@lem6776900 K j k) (@lem6776904 K j k)). Qed.
Lemma lem6776907 {K : Type'} (j : K) (k : K -> Prop) : (term588 K j k) = (term589 K j k).
Proof. exact (MK_COMB (@lem6776889) (@lem6776906 K j k)). Qed.
Lemma lem6776908 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6776909 {K : Type'} (j : K) (k : K -> Prop) : (term590 K j k) = (term591 K j k).
Proof. exact (MK_COMB (@lem6776908) (@lem6776907 K j k)). Qed.
Lemma lem6776910 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term495 K k ltle j i) = (term592 K k ltle j i).
Proof. exact (MK_COMB (@lem6776909 K j k) (@lem6776888 K ltle j i)). Qed.
Lemma lem6776911 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term497 K k ltle i) = (term593 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6776910 K k ltle j i)). Qed.
Lemma lem6776912 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6776913 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term498 K k ltle i) = (term594 K k ltle i).
Proof. exact (MK_COMB (@lem6776912 K) (@lem6776911 K k ltle i)). Qed.
Lemma lem6776914 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term594 K k ltle i.
Proof. exact (EQ_MP (@lem6776913 K k ltle i) (@lem6776582 K k ltle i h1)). Qed.
Lemma lem6776921 {K : Type'} (j : K) (i : K) : (term595 K j i) = (term595 K j i).
Proof. exact (eq_refl (term595 K j i)). Qed.
Lemma lem6776922 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem6776927 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776928 {A K : Type'} (f : K -> A) (x : K) : (f x) = (@I (K -> A) f x).
Proof. exact (@lem6776927 K A f x). Qed.
Lemma lem6776930 {A K : Type'} (f : K -> A) (j : K) : (f j) = (@I (K -> A) f j).
Proof. exact (@lem6776928 A K f j). Qed.
Lemma lem6776939 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776940 {A : Type'} (f : type1363 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6776939 A (type672 A) f x). Qed.
Lemma lem6776941 {A : Type'} (neut : A) : (@INSERT A neut) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) neut).
Proof. exact (@lem6776940 A (@INSERT A) neut). Qed.
Lemma lem6776942 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem6776943 {A : Type'} (neut : A) : (@INSERT A neut (@EMPTY A)) = (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) neut (@EMPTY A)).
Proof. exact (MK_COMB (@lem6776941 A neut) (@lem6776942 A)). Qed.
Lemma lem6776945 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776946 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6776945 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem6776947 {A : Type'} (neut : A) : (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) neut (@EMPTY A)) = (term596 A neut).
Proof. exact (@lem6776946 A (@I (A -> (A -> Prop) -> A -> Prop) (@INSERT A) neut) (@EMPTY A)). Qed.
Lemma lem6776949 {A : Type'} (neut : A) : (@INSERT A neut (@EMPTY A)) = (term596 A neut).
Proof. exact (TRANS (@lem6776943 A neut) (@lem6776947 A neut)). Qed.
Lemma lem6776950 {A : Type'} (dom : A -> Prop) : (@DIFF A dom) = (@DIFF A dom).
Proof. exact (eq_refl (@DIFF A dom)). Qed.
Lemma lem6776951 {A : Type'} (dom : A -> Prop) (neut : A) : (term597 A dom neut) = (term598 A dom neut).
Proof. exact (MK_COMB (@lem6776950 A dom) (@lem6776949 A neut)). Qed.
Lemma lem6776953 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776954 {A : Type'} (f : type636 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6776953 (A -> Prop) (type672 A) f x). Qed.
Lemma lem6776955 {A : Type'} (dom : A -> Prop) : (@DIFF A dom) = (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@DIFF A) dom).
Proof. exact (@lem6776954 A (@DIFF A) dom). Qed.
Lemma lem6776956 {A : Type'} (neut : A) : (term596 A neut) = (term596 A neut).
Proof. exact (eq_refl (term596 A neut)). Qed.
Lemma lem6776957 {A : Type'} (dom : A -> Prop) (neut : A) : (term598 A dom neut) = (term599 A dom neut).
Proof. exact (MK_COMB (@lem6776955 A dom) (@lem6776956 A neut)). Qed.
Lemma lem6776959 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776960 {A : Type'} (f : type672 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> Prop) f x).
Proof. exact (@lem6776959 (A -> Prop) (A -> Prop) f x). Qed.
Lemma lem6776961 {A : Type'} (dom : A -> Prop) (neut : A) : (term599 A dom neut) = (term600 A dom neut).
Proof. exact (@lem6776960 A (@I ((A -> Prop) -> (A -> Prop) -> A -> Prop) (@DIFF A) dom) (term596 A neut)). Qed.
Lemma lem6776962 {A : Type'} (dom : A -> Prop) (neut : A) : (term598 A dom neut) = (term600 A dom neut).
Proof. exact (TRANS (@lem6776957 A dom neut) (@lem6776961 A dom neut)). Qed.
Lemma lem6776963 {A : Type'} (dom : A -> Prop) (neut : A) : (term597 A dom neut) = (term600 A dom neut).
Proof. exact (TRANS (@lem6776951 A dom neut) (@lem6776962 A dom neut)). Qed.
Lemma lem6776964 {A K : Type'} (f : K -> A) (j : K) : (term601 A K f j) = (term602 A K f j).
Proof. exact (MK_COMB (@lem6776922 A) (@lem6776930 A K f j)). Qed.
Lemma lem6776965 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term603 A K f j dom neut) = (term604 A K f j dom neut).
Proof. exact (MK_COMB (@lem6776964 A K f j) (@lem6776963 A dom neut)). Qed.
Lemma lem6776967 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776968 {A : Type'} (f : type1364 A) (x : A) : (f x) = (@I (A -> (A -> Prop) -> Prop) f x).
Proof. exact (@lem6776967 A (type686 A) f x). Qed.
Lemma lem6776969 {A K : Type'} (f : K -> A) (j : K) : (term602 A K f j) = (term605 A K f j).
Proof. exact (@lem6776968 A (@IN A) (@I (K -> A) f j)). Qed.
Lemma lem6776970 {A : Type'} (dom : A -> Prop) (neut : A) : (term600 A dom neut) = (term600 A dom neut).
Proof. exact (eq_refl (term600 A dom neut)). Qed.
Lemma lem6776971 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term604 A K f j dom neut) = (term606 A K f j dom neut).
Proof. exact (MK_COMB (@lem6776969 A K f j) (@lem6776970 A dom neut)). Qed.
Lemma lem6776973 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776974 {A : Type'} (f : type686 A) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> Prop) f x).
Proof. exact (@lem6776973 (A -> Prop) Prop f x). Qed.
Lemma lem6776975 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term606 A K f j dom neut) = (term607 A K f j dom neut).
Proof. exact (@lem6776974 A (term605 A K f j) (term600 A dom neut)). Qed.
Lemma lem6776976 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term604 A K f j dom neut) = (term607 A K f j dom neut).
Proof. exact (TRANS (@lem6776971 A K f j dom neut) (@lem6776975 A K f j dom neut)). Qed.
Lemma lem6776977 {A K : Type'} (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term603 A K f j dom neut) = (term607 A K f j dom neut).
Proof. exact (TRANS (@lem6776965 A K f j dom neut) (@lem6776976 A K f j dom neut)). Qed.
Lemma lem6776984 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776985 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem6776984 K (type686 K) f x). Qed.
Lemma lem6776986 {K : Type'} (j : K) : (@IN K j) = (@I (K -> (K -> Prop) -> Prop) (@IN K) j).
Proof. exact (@lem6776985 K (@IN K) j). Qed.
Lemma lem6776987 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6776988 {K : Type'} (j : K) (k : K -> Prop) : (@IN K j k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) j k).
Proof. exact (MK_COMB (@lem6776986 K j) (@lem6776987 K k)). Qed.
Lemma lem6776990 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6776991 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem6776990 (K -> Prop) Prop f x). Qed.
Lemma lem6776992 {K : Type'} (j : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) j k) = (term587 K j k).
Proof. exact (@lem6776991 K (@I (K -> (K -> Prop) -> Prop) (@IN K) j) k). Qed.
Lemma lem6776994 {K : Type'} (j : K) (k : K -> Prop) : (@IN K j k) = (term587 K j k).
Proof. exact (TRANS (@lem6776988 K j k) (@lem6776992 K j k)). Qed.
Lemma lem6776995 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6776996 {K : Type'} (j : K) (k : K -> Prop) : (term506 K j k) = (term608 K j k).
Proof. exact (MK_COMB (@lem6776995) (@lem6776994 K j k)). Qed.
Lemma lem6776997 {A K : Type'} (k : K -> Prop) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term609 A K k f j dom neut) = (term610 A K k f j dom neut).
Proof. exact (MK_COMB (@lem6776996 K j k) (@lem6776977 A K f j dom neut)). Qed.
Lemma lem6777004 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777005 {K : Type'} (f : type1402 K) (x : K) : (f x) = (@I (K -> K -> Prop) f x).
Proof. exact (@lem6777004 K (K -> Prop) f x). Qed.
Lemma lem6777006 {K : Type'} (ltle : type1402 K) (j : K) : (ltle j) = (@I (K -> K -> Prop) ltle j).
Proof. exact (@lem6777005 K ltle j). Qed.
Lemma lem6777007 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6777008 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (ltle j i) = (@I (K -> K -> Prop) ltle j i).
Proof. exact (MK_COMB (@lem6777006 K ltle j) (@lem6777007 K i)). Qed.
Lemma lem6777010 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777011 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6777010 K Prop f x). Qed.
Lemma lem6777012 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (@I (K -> K -> Prop) ltle j i) = (term581 K ltle j i).
Proof. exact (@lem6777011 K (@I (K -> K -> Prop) ltle j) i). Qed.
Lemma lem6777014 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (ltle j i) = (term581 K ltle j i).
Proof. exact (TRANS (@lem6777008 K ltle j i) (@lem6777012 K ltle j i)). Qed.
Lemma lem6777015 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6777016 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term584 K ltle j i) = (term585 K ltle j i).
Proof. exact (MK_COMB (@lem6777015) (@lem6777014 K ltle j i)). Qed.
Lemma lem6777017 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term522 A K ltle i k f j dom neut) = (term611 A K ltle i k f j dom neut).
Proof. exact (MK_COMB (@lem6777016 K ltle j i) (@lem6776997 A K k f j dom neut)). Qed.
Lemma lem6777018 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6777019 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (j : K) (dom : A -> Prop) (neut : A) : (term612 A K ltle i k f j dom neut) = (term613 A K ltle i k f j dom neut).
Proof. exact (MK_COMB (@lem6777018) (@lem6777017 A K ltle i k f j dom neut)). Qed.
Lemma lem6777020 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term521 A K ltle k f dom neut j i) = (term614 A K ltle k f dom neut j i).
Proof. exact (MK_COMB (@lem6777019 A K ltle i k f j dom neut) (@lem6776921 K j i)). Qed.
Lemma lem6777021 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6777028 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777029 {K : Type'} (f : type1402 K) (x : K) : (f x) = (@I (K -> K -> Prop) f x).
Proof. exact (@lem6777028 K (K -> Prop) f x). Qed.
Lemma lem6777030 {K : Type'} (ltle : type1402 K) (j : K) : (ltle j) = (@I (K -> K -> Prop) ltle j).
Proof. exact (@lem6777029 K ltle j). Qed.
Lemma lem6777031 {K : Type'} (i : K) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem6777032 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (ltle j i) = (@I (K -> K -> Prop) ltle j i).
Proof. exact (MK_COMB (@lem6777030 K ltle j) (@lem6777031 K i)). Qed.
Lemma lem6777034 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777035 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6777034 K Prop f x). Qed.
Lemma lem6777036 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (@I (K -> K -> Prop) ltle j i) = (term581 K ltle j i).
Proof. exact (@lem6777035 K (@I (K -> K -> Prop) ltle j) i). Qed.
Lemma lem6777038 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (ltle j i) = (term581 K ltle j i).
Proof. exact (TRANS (@lem6777032 K ltle j i) (@lem6777036 K ltle j i)). Qed.
Lemma lem6777039 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term582 K ltle j i) = (term583 K ltle j i).
Proof. exact (MK_COMB (@lem6777021) (@lem6777038 K ltle j i)). Qed.
Lemma lem6777040 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6777047 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777048 {K : Type'} (f : type1402 K) (x : K) : (f x) = (@I (K -> K -> Prop) f x).
Proof. exact (@lem6777047 K (K -> Prop) f x). Qed.
Lemma lem6777049 {K : Type'} (ltle : type1402 K) (i : K) : (ltle i) = (@I (K -> K -> Prop) ltle i).
Proof. exact (@lem6777048 K ltle i). Qed.
Lemma lem6777050 {K : Type'} (j : K) : j = j.
Proof. exact (eq_refl j). Qed.
Lemma lem6777051 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (ltle i j) = (@I (K -> K -> Prop) ltle i j).
Proof. exact (MK_COMB (@lem6777049 K ltle i) (@lem6777050 K j)). Qed.
Lemma lem6777053 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777054 {K : Type'} (f : K -> Prop) (x : K) : (f x) = (@I (K -> Prop) f x).
Proof. exact (@lem6777053 K Prop f x). Qed.
Lemma lem6777055 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (@I (K -> K -> Prop) ltle i j) = (term581 K ltle i j).
Proof. exact (@lem6777054 K (@I (K -> K -> Prop) ltle i) j). Qed.
Lemma lem6777057 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (ltle i j) = (term581 K ltle i j).
Proof. exact (TRANS (@lem6777051 K ltle i j) (@lem6777055 K ltle i j)). Qed.
Lemma lem6777058 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (term582 K ltle i j) = (term583 K ltle i j).
Proof. exact (MK_COMB (@lem6777040) (@lem6777057 K ltle i j)). Qed.
Lemma lem6777059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6777060 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (term615 K ltle i j) = (term616 K ltle i j).
Proof. exact (MK_COMB (@lem6777059) (@lem6777058 K ltle i j)). Qed.
Lemma lem6777061 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term500 K ltle j i) = (term617 K ltle j i).
Proof. exact (MK_COMB (@lem6777060 K ltle i j) (@lem6777039 K ltle j i)). Qed.
Lemma lem6777070 {K : Type'} (i : K) (j : K) : (term501 K i j) = (term501 K i j).
Proof. exact (eq_refl (term501 K i j)). Qed.
Lemma lem6777071 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term503 K ltle j i) = (term618 K ltle j i).
Proof. exact (MK_COMB (@lem6777070 K i j) (@lem6777061 K ltle j i)). Qed.
Lemma lem6777078 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777079 {K : Type'} (f : type1364 K) (x : K) : (f x) = (@I (K -> (K -> Prop) -> Prop) f x).
Proof. exact (@lem6777078 K (type686 K) f x). Qed.
Lemma lem6777080 {K : Type'} (j : K) : (@IN K j) = (@I (K -> (K -> Prop) -> Prop) (@IN K) j).
Proof. exact (@lem6777079 K (@IN K) j). Qed.
Lemma lem6777081 {K : Type'} (k : K -> Prop) : k = k.
Proof. exact (eq_refl k). Qed.
Lemma lem6777082 {K : Type'} (j : K) (k : K -> Prop) : (@IN K j k) = (@I (K -> (K -> Prop) -> Prop) (@IN K) j k).
Proof. exact (MK_COMB (@lem6777080 K j) (@lem6777081 K k)). Qed.
Lemma lem6777084 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777085 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem6777084 (K -> Prop) Prop f x). Qed.
Lemma lem6777086 {K : Type'} (j : K) (k : K -> Prop) : (@I (K -> (K -> Prop) -> Prop) (@IN K) j k) = (term587 K j k).
Proof. exact (@lem6777085 K (@I (K -> (K -> Prop) -> Prop) (@IN K) j) k). Qed.
Lemma lem6777088 {K : Type'} (j : K) (k : K -> Prop) : (@IN K j k) = (term587 K j k).
Proof. exact (TRANS (@lem6777082 K j k) (@lem6777086 K j k)). Qed.
Lemma lem6777089 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6777090 {K : Type'} (j : K) (k : K -> Prop) : (term506 K j k) = (term608 K j k).
Proof. exact (MK_COMB (@lem6777089) (@lem6777088 K j k)). Qed.
Lemma lem6777091 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term508 K k ltle j i) = (term619 K k ltle j i).
Proof. exact (MK_COMB (@lem6777090 K j k) (@lem6777071 K ltle j i)). Qed.
Lemma lem6777092 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6777093 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term552 K k ltle j i) = (term620 K k ltle j i).
Proof. exact (MK_COMB (@lem6777092) (@lem6777091 K k ltle j i)). Qed.
Lemma lem6777094 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term554 A K ltle k f dom neut j i) = (term621 A K ltle k f dom neut j i).
Proof. exact (MK_COMB (@lem6777093 K k ltle j i) (@lem6777020 A K ltle k f dom neut j i)). Qed.
Lemma lem6777095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6777096 {K : Type'} : (@FINITE K) = (@FINITE K).
Proof. exact (eq_refl (@FINITE K)). Qed.
Lemma lem6777097 {K : Type'} : (@GSPEC K) = (@GSPEC K).
Proof. exact (eq_refl (@GSPEC K)). Qed.
Lemma lem6777108 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777109 {A K : Type'} (f : type849 A K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) f x).
Proof. exact (@lem6777108 (K -> Prop) (type781 A K) f x). Qed.
Lemma lem6777110 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) : (_88612 k) = (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k).
Proof. exact (@lem6777109 A K _88612 k). Qed.
Lemma lem6777111 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem6777112 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (_88612 k f) = (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k f).
Proof. exact (MK_COMB (@lem6777110 A K _88612 k) (@lem6777111 A K f)). Qed.
Lemma lem6777114 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777115 {A K : Type'} (f : type781 A K) (x : K -> A) : (f x) = (@I ((K -> A) -> (A -> Prop) -> A -> K -> Prop) f x).
Proof. exact (@lem6777114 (K -> A) (type669 A K) f x). Qed.
Lemma lem6777116 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k f) = (term572 A K _88612 k f).
Proof. exact (@lem6777115 A K (@I ((K -> Prop) -> (K -> A) -> (A -> Prop) -> A -> K -> Prop) _88612 k) f). Qed.
Lemma lem6777117 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) : (_88612 k f) = (term572 A K _88612 k f).
Proof. exact (TRANS (@lem6777112 A K _88612 k f) (@lem6777116 A K _88612 k f)). Qed.
Lemma lem6777118 {A : Type'} (dom : A -> Prop) : dom = dom.
Proof. exact (eq_refl dom). Qed.
Lemma lem6777119 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (_88612 k f dom) = (term573 A K _88612 k f dom).
Proof. exact (MK_COMB (@lem6777117 A K _88612 k f) (@lem6777118 A dom)). Qed.
Lemma lem6777121 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777122 {A K : Type'} (f : type669 A K) (x : A -> Prop) : (f x) = (@I ((A -> Prop) -> A -> K -> Prop) f x).
Proof. exact (@lem6777121 (A -> Prop) (type1413 A K) f x). Qed.
Lemma lem6777123 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (term573 A K _88612 k f dom) = (term574 A K _88612 k f dom).
Proof. exact (@lem6777122 A K (term572 A K _88612 k f) dom). Qed.
Lemma lem6777124 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) : (_88612 k f dom) = (term574 A K _88612 k f dom).
Proof. exact (TRANS (@lem6777119 A K _88612 k f dom) (@lem6777123 A K _88612 k f dom)). Qed.
Lemma lem6777125 {A : Type'} (neut : A) : neut = neut.
Proof. exact (eq_refl neut). Qed.
Lemma lem6777126 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (_88612 k f dom neut) = (term575 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6777124 A K _88612 k f dom) (@lem6777125 A neut)). Qed.
Lemma lem6777128 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777129 {A K : Type'} (f : type1413 A K) (x : A) : (f x) = (@I (A -> K -> Prop) f x).
Proof. exact (@lem6777128 A (K -> Prop) f x). Qed.
Lemma lem6777130 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term575 A K _88612 k f dom neut) = (term576 A K _88612 k f dom neut).
Proof. exact (@lem6777129 A K (term574 A K _88612 k f dom) neut). Qed.
Lemma lem6777132 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (_88612 k f dom neut) = (term576 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6777126 A K _88612 k f dom neut) (@lem6777130 A K _88612 k f dom neut)). Qed.
Lemma lem6777133 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term84 A K _88612 k f dom neut) = (term577 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6777097 K) (@lem6777132 A K _88612 k f dom neut)). Qed.
Lemma lem6777135 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777136 {K : Type'} (f : type672 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> K -> Prop) f x).
Proof. exact (@lem6777135 (K -> Prop) (K -> Prop) f x). Qed.
Lemma lem6777137 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term577 A K _88612 k f dom neut) = (term578 A K _88612 k f dom neut).
Proof. exact (@lem6777136 K (@GSPEC K) (term576 A K _88612 k f dom neut)). Qed.
Lemma lem6777138 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term84 A K _88612 k f dom neut) = (term578 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6777133 A K _88612 k f dom neut) (@lem6777137 A K _88612 k f dom neut)). Qed.
Lemma lem6777139 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term85 A K _88612 k f dom neut) = (term579 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6777096 K) (@lem6777138 A K _88612 k f dom neut)). Qed.
Lemma lem6777141 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem6777142 {K : Type'} (f : type686 K) (x : K -> Prop) : (f x) = (@I ((K -> Prop) -> Prop) f x).
Proof. exact (@lem6777141 (K -> Prop) Prop f x). Qed.
Lemma lem6777143 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term579 A K _88612 k f dom neut) = (term580 A K _88612 k f dom neut).
Proof. exact (@lem6777142 K (@FINITE K) (term578 A K _88612 k f dom neut)). Qed.
Lemma lem6777144 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term85 A K _88612 k f dom neut) = (term580 A K _88612 k f dom neut).
Proof. exact (TRANS (@lem6777139 A K _88612 k f dom neut) (@lem6777143 A K _88612 k f dom neut)). Qed.
Lemma lem6777145 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term561 A K _88612 k f dom neut) = (term622 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6777095) (@lem6777144 A K _88612 k f dom neut)). Qed.
Lemma lem6777146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6777147 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term535 A K _88612 k f dom neut) = (term623 A K _88612 k f dom neut).
Proof. exact (MK_COMB (@lem6777146) (@lem6777145 A K _88612 k f dom neut)). Qed.
Lemma lem6777148 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) : (term568 A K _88612 ltle k f dom neut j i) = (term624 A K _88612 ltle k f dom neut j i).
Proof. exact (MK_COMB (@lem6777147 A K _88612 k f dom neut) (@lem6777094 A K ltle k f dom neut j i)). Qed.
Lemma lem6777149 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term568 A K _88612 ltle k f dom neut j i) : term624 A K _88612 ltle k f dom neut j i.
Proof. exact (EQ_MP (@lem6777148 A K _88612 ltle k f dom neut j i) (@lem6776798 A K _88612 ltle k f dom neut j i h1)). Qed.
Lemma lem6777619 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term621 A K ltle k f dom neut j i) : term621 A K ltle k f dom neut j i.
Proof. exact (h1). Qed.
Lemma lem6777620 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term619 K k ltle j i.
Proof. exact (h1). Qed.
Lemma lem6777621 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term614 A K ltle k f dom neut j i.
Proof. exact (h1). Qed.
Lemma lem6777622 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term618 K ltle j i.
Proof. exact (proj2 (@lem6777620 K k ltle j i h1)). Qed.
Lemma lem6777624 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term617 K ltle j i.
Proof. exact (proj2 (@lem6777622 K k ltle j i h1)). Qed.
Lemma lem6777629 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term611 A K ltle i k f j dom neut.
Proof. exact (proj1 (@lem6777621 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6777630 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term610 A K k f j dom neut.
Proof. exact (proj2 (@lem6777629 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6777751 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term622 A K _88612 k f dom neut) : term622 A K _88612 k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6777773 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term592 K k ltle j i) = (term625 K k ltle j i).
Proof. exact (@lem19490 (term581 K ltle i j) (term589 K j k) (term583 K ltle j i)). Qed.
Lemma lem6777774 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term593 K k ltle i) = (term626 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6777773 K k ltle j i)). Qed.
Lemma lem6777775 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6777777 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term594 K k ltle i) = (term627 K k ltle i).
Proof. exact (MK_COMB (@lem6777775 K) (@lem6777774 K k ltle i)). Qed.
Lemma lem6777778 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term627 K k ltle i.
Proof. exact (EQ_MP (@lem6777777 K k ltle i) (@lem6776914 K k ltle i h1)). Qed.
Lemma lem6777903 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) : (term592 K k ltle j i) = (term625 K k ltle j i).
Proof. exact (@lem19490 (term581 K ltle i j) (term589 K j k) (term583 K ltle j i)). Qed.
Lemma lem6777904 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term593 K k ltle i) = (term626 K k ltle i).
Proof. exact (fun_ext (fun j : K => @lem6777903 K k ltle j i)). Qed.
Lemma lem6777905 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem6777907 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) : (term594 K k ltle i) = (term627 K k ltle i).
Proof. exact (MK_COMB (@lem6777905 K) (@lem6777904 K k ltle i)). Qed.
Lemma lem6777908 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term627 K k ltle i.
Proof. exact (EQ_MP (@lem6777907 K k ltle i) (@lem6776914 K k ltle i h1)). Qed.
Lemma lem6778048 {K : Type'} (_88625 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term628 K k ltle i _88625.
Proof. exact (@lem6777778 K k ltle i h1 _88625). Qed.
Lemma lem6778049 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (_88625 : K) (i : K) : (term628 K k ltle i _88625) = (term625 K k ltle _88625 i).
Proof. exact (eq_refl (term628 K k ltle i _88625)). Qed.
Lemma lem6778050 {K : Type'} (_88625 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term625 K k ltle _88625 i.
Proof. exact (EQ_MP (@lem6778049 K k ltle _88625 i) (@lem6778048 K _88625 k ltle i h1)). Qed.
Lemma lem6778084 {K : Type'} (_88637 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term628 K k ltle i _88637.
Proof. exact (@lem6777908 K k ltle i h1 _88637). Qed.
Lemma lem6778085 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (_88637 : K) (i : K) : (term628 K k ltle i _88637) = (term625 K k ltle _88637 i).
Proof. exact (eq_refl (term628 K k ltle i _88637)). Qed.
Lemma lem6778086 {K : Type'} (_88637 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term625 K k ltle _88637 i.
Proof. exact (EQ_MP (@lem6778085 K k ltle _88637 i) (@lem6778084 K _88637 k ltle i h1)). Qed.
Lemma lem6778141 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term622 A K _88612 k f dom neut) : term622 A K _88612 k f dom neut.
Proof. exact (h1). Qed.
Lemma lem6778173 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term583 K ltle i j.
Proof. exact (proj1 (@lem6777624 K k ltle j i h1)). Qed.
Lemma lem6778181 {K : Type'} (_88625 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term629 K k ltle i _88625.
Proof. exact (proj1 (@lem6778050 K _88625 k ltle i h1)). Qed.
Lemma lem6778221 {K : Type'} (_88637 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term630 K k ltle _88637 i.
Proof. exact (proj2 (@lem6778086 K _88637 k ltle i h1)). Qed.
Lemma lem6778223 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) : term580 A K _88612 k f dom neut.
Proof. exact (EQ_MP (@lem6776848 A K _88612 k f dom neut) (@lem6776515 A K _88612 k f dom neut h1)). Qed.
Lemma lem6778224 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) : term631 A K _88612 k f dom neut.
Proof. exact (fun h0 : term622 A K _88612 k f dom neut => @lem6778223 A K _88612 k f dom neut h1). Qed.
Lemma lem6778226 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6778227 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term631 A K _88612 k f dom neut) = (term580 A K _88612 k f dom neut).
Proof. exact (@lem6778226 (term580 A K _88612 k f dom neut)). Qed.
Lemma lem6778228 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) : term580 A K _88612 k f dom neut.
Proof. exact (EQ_MP (@lem6778227 A K _88612 k f dom neut) (@lem6778224 A K _88612 k f dom neut h1)). Qed.
Lemma lem6778231 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6778233 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) : (term622 A K _88612 k f dom neut) = (term633 A K _88612 k f dom neut).
Proof. exact (@lem6778231 (term580 A K _88612 k f dom neut)). Qed.
Lemma lem6778236 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term622 A K _88612 k f dom neut) : term633 A K _88612 k f dom neut.
Proof. exact (EQ_MP (@lem6778233 A K _88612 k f dom neut) (@lem6778141 A K _88612 k f dom neut h1)). Qed.
Lemma lem6778239 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : False.
Proof. exact (@lem6778236 A K _88612 k f dom neut h2 (@lem6778228 A K _88612 k f dom neut h1)). Qed.
Lemma lem6778240 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : term634.
Proof. exact (fun h0 : ~ False => @lem6778239 A K _88612 k f dom neut h1 h2). Qed.
Lemma lem6778242 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6778243 : term634 = False.
Proof. exact (@lem6778242 False). Qed.
Lemma lem6778244 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : False.
Proof. exact (EQ_MP (@lem6778243) (@lem6778240 A K _88612 k f dom neut h1 h2)). Qed.
Lemma lem6778664 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term587 K j k.
Proof. exact (proj1 (@lem6777620 K k ltle j i h1)). Qed.
Lemma lem6778665 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term635 K j k.
Proof. exact (fun h0 : term589 K j k => @lem6778664 K k ltle j i h1). Qed.
Lemma lem6778667 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6778668 {K : Type'} (j : K) (k : K -> Prop) : (term635 K j k) = (term587 K j k).
Proof. exact (@lem6778667 (term587 K j k)). Qed.
Lemma lem6778669 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term587 K j k.
Proof. exact (EQ_MP (@lem6778668 K j k) (@lem6778665 K k ltle j i h1)). Qed.
Lemma lem6778675 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem6778676 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : (term629 K k ltle i _88625) = (term636 K ltle i _88625 k).
Proof. exact (@lem6778675 (term581 K ltle i _88625) (term589 K _88625 k)). Qed.
Lemma lem6778682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6778683 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : (term637 K k ltle i _88625) = (term638 K ltle i _88625 k).
Proof. exact (MK_COMB (@lem6778682) (@lem6778676 K ltle i _88625 k)). Qed.
Lemma lem6778689 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : (term636 K ltle i _88625 k) = (term636 K ltle i _88625 k).
Proof. exact (eq_refl (term636 K ltle i _88625 k)). Qed.
Lemma lem6778690 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : ((term629 K k ltle i _88625) = (term636 K ltle i _88625 k)) = ((term636 K ltle i _88625 k) = (term636 K ltle i _88625 k)).
Proof. exact (MK_COMB (@lem6778683 K ltle i _88625 k) (@lem6778689 K ltle i _88625 k)). Qed.
Lemma lem6778692 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem6778693 (x : Prop) : (x = x) = True.
Proof. exact (@lem6778692 Prop x). Qed.
Lemma lem6778694 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : ((term636 K ltle i _88625 k) = (term636 K ltle i _88625 k)) = True.
Proof. exact (@lem6778693 (term636 K ltle i _88625 k)). Qed.
Lemma lem6778695 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : ((term629 K k ltle i _88625) = (term636 K ltle i _88625 k)) = True.
Proof. exact (TRANS (@lem6778690 K ltle i _88625 k) (@lem6778694 K ltle i _88625 k)). Qed.
Lemma lem6778696 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : True = ((term629 K k ltle i _88625) = (term636 K ltle i _88625 k)).
Proof. exact (SYM (@lem6778695 K ltle i _88625 k)). Qed.
Lemma lem6778697 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) (k : K -> Prop) : (term629 K k ltle i _88625) = (term636 K ltle i _88625 k).
Proof. exact (EQ_MP (@lem6778696 K ltle i _88625 k) (@lem0)). Qed.
Lemma lem6778698 {K : Type'} (_88625 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term636 K ltle i _88625 k.
Proof. exact (EQ_MP (@lem6778697 K ltle i _88625 k) (@lem6778181 K _88625 k ltle i h1)). Qed.
Lemma lem6778700 (b : Prop) (a : Prop) : (a \/ b) = (term639 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem6778701 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (_88625 : K) : (term636 K ltle i _88625 k) = (term640 K k ltle i _88625).
Proof. exact (@lem6778700 (term589 K _88625 k) (term581 K ltle i _88625)). Qed.
Lemma lem6778703 (a : Prop) : (term32 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem6778704 {K : Type'} (_88625 : K) (k : K -> Prop) : (term641 K _88625 k) = (term587 K _88625 k).
Proof. exact (@lem6778703 (term587 K _88625 k)). Qed.
Lemma lem6778705 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem6778706 {K : Type'} (_88625 : K) (k : K -> Prop) : (term642 K _88625 k) = (term643 K _88625 k).
Proof. exact (MK_COMB (@lem6778705) (@lem6778704 K _88625 k)). Qed.
Lemma lem6778707 {K : Type'} (ltle : type1402 K) (i : K) (_88625 : K) : (term581 K ltle i _88625) = (term581 K ltle i _88625).
Proof. exact (eq_refl (term581 K ltle i _88625)). Qed.
Lemma lem6778708 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (_88625 : K) : (term640 K k ltle i _88625) = (term644 K k ltle i _88625).
Proof. exact (MK_COMB (@lem6778706 K _88625 k) (@lem6778707 K ltle i _88625)). Qed.
Lemma lem6778709 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (i : K) (_88625 : K) : (term636 K ltle i _88625 k) = (term644 K k ltle i _88625).
Proof. exact (TRANS (@lem6778701 K k ltle i _88625) (@lem6778708 K k ltle i _88625)). Qed.
Lemma lem6778712 {K : Type'} (_88625 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term644 K k ltle i _88625.
Proof. exact (EQ_MP (@lem6778709 K k ltle i _88625) (@lem6778698 K _88625 k ltle i h1)). Qed.
Lemma lem6778713 {K : Type'} (_88625 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term644 K k ltle i _88625.
Proof. exact (@lem6778712 K _88625 k ltle i h1). Qed.
Lemma lem6778714 {K : Type'} (j : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term644 K k ltle i j.
Proof. exact (@lem6778713 K j k ltle i h1). Qed.
Lemma lem6778717 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term619 K k ltle j i) : term581 K ltle i j.
Proof. exact (@lem6778714 K j k ltle i h1 (@lem6778669 K k ltle j i h2)). Qed.
Lemma lem6778718 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term619 K k ltle j i) : term645 K ltle i j.
Proof. exact (fun h0 : term583 K ltle i j => @lem6778717 K k ltle j i h1 h2). Qed.
Lemma lem6778720 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6778721 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (term645 K ltle i j) = (term581 K ltle i j).
Proof. exact (@lem6778720 (term581 K ltle i j)). Qed.
Lemma lem6778722 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term619 K k ltle j i) : term581 K ltle i j.
Proof. exact (EQ_MP (@lem6778721 K ltle i j) (@lem6778718 K k ltle j i h1 h2)). Qed.
Lemma lem6778725 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6778727 {K : Type'} (ltle : type1402 K) (i : K) (j : K) : (term583 K ltle i j) = (term646 K ltle i j).
Proof. exact (@lem6778725 (term581 K ltle i j)). Qed.
Lemma lem6778730 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term619 K k ltle j i) : term646 K ltle i j.
Proof. exact (EQ_MP (@lem6778727 K ltle i j) (@lem6778173 K k ltle j i h1)). Qed.
Lemma lem6778733 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term619 K k ltle j i) : False.
Proof. exact (@lem6778730 K k ltle j i h2 (@lem6778722 K k ltle j i h1 h2)). Qed.
Lemma lem6778734 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term619 K k ltle j i) : term634.
Proof. exact (fun h0 : ~ False => @lem6778733 K k ltle j i h1 h2). Qed.
Lemma lem6778736 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6778737 : term634 = False.
Proof. exact (@lem6778736 False). Qed.
Lemma lem6778738 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term619 K k ltle j i) : False.
Proof. exact (EQ_MP (@lem6778737) (@lem6778734 K k ltle j i h1 h2)). Qed.
Lemma lem6779177 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term587 K j k.
Proof. exact (proj1 (@lem6777630 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6779178 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term635 K j k.
Proof. exact (fun h0 : term589 K j k => @lem6779177 A K ltle k f dom neut j i h1). Qed.
Lemma lem6779180 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779181 {K : Type'} (j : K) (k : K -> Prop) : (term635 K j k) = (term587 K j k).
Proof. exact (@lem6779180 (term587 K j k)). Qed.
Lemma lem6779182 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term587 K j k.
Proof. exact (EQ_MP (@lem6779181 K j k) (@lem6779178 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6779184 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term581 K ltle j i.
Proof. exact (proj1 (@lem6777629 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6779185 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term645 K ltle j i.
Proof. exact (fun h0 : term583 K ltle j i => @lem6779184 A K ltle k f dom neut j i h1). Qed.
Lemma lem6779187 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779188 {K : Type'} (ltle : type1402 K) (j : K) (i : K) : (term645 K ltle j i) = (term581 K ltle j i).
Proof. exact (@lem6779187 (term581 K ltle j i)). Qed.
Lemma lem6779189 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term581 K ltle j i.
Proof. exact (EQ_MP (@lem6779188 K ltle j i) (@lem6779185 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6779191 (a : Prop) (b : Prop) : (term647 a b) = (term648 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem6779192 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (_88637 : K) (i : K) : (term630 K k ltle _88637 i) = (term649 K k ltle _88637 i).
Proof. exact (@lem6779191 (term587 K _88637 k) (term581 K ltle _88637 i)). Qed.
Lemma lem6779194 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem6779195 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (_88637 : K) (i : K) : (term649 K k ltle _88637 i) = (term650 K k ltle _88637 i).
Proof. exact (@lem6779194 (term651 K k ltle _88637 i)). Qed.
Lemma lem6779196 {K : Type'} (k : K -> Prop) (ltle : type1402 K) (_88637 : K) (i : K) : (term630 K k ltle _88637 i) = (term650 K k ltle _88637 i).
Proof. exact (TRANS (@lem6779192 K k ltle _88637 i) (@lem6779195 K k ltle _88637 i)). Qed.
Lemma lem6779198 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term614 A K ltle k f dom neut j i) : term651 K k ltle j i.
Proof. exact (conj (@lem6779182 A K ltle k f dom neut j i h1) (@lem6779189 A K ltle k f dom neut j i h1)). Qed.
Lemma lem6779200 {K : Type'} (_88637 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term650 K k ltle _88637 i.
Proof. exact (EQ_MP (@lem6779196 K k ltle _88637 i) (@lem6778221 K _88637 k ltle i h1)). Qed.
Lemma lem6779201 {K : Type'} (_88637 : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term650 K k ltle _88637 i.
Proof. exact (@lem6779200 K _88637 k ltle i h1). Qed.
Lemma lem6779202 {K : Type'} (j : K) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term21 K k ltle i) : term650 K k ltle j i.
Proof. exact (@lem6779201 K j k ltle i h1). Qed.
Lemma lem6779205 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term614 A K ltle k f dom neut j i) : False.
Proof. exact (@lem6779202 K j k ltle i h1 (@lem6779198 A K ltle k f dom neut j i h2)). Qed.
Lemma lem6779206 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term614 A K ltle k f dom neut j i) : term634.
Proof. exact (fun h0 : ~ False => @lem6779205 A K ltle k f dom neut j i h1 h2). Qed.
Lemma lem6779208 (p : Prop) : (term632 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem6779209 : term634 = False.
Proof. exact (@lem6779208 False). Qed.
Lemma lem6779210 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term614 A K ltle k f dom neut j i) : False.
Proof. exact (EQ_MP (@lem6779209) (@lem6779206 A K ltle k f dom neut j i h1 h2)). Qed.
Lemma lem6779211 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : (term622 A K _88612 k f dom neut) = False.
Proof. exact (prop_ext (fun h3 : term622 A K _88612 k f dom neut => @lem6778244 A K _88612 k f dom neut h1 h2) (fun h3 : False => @lem6778141 A K _88612 k f dom neut h2)). Qed.
Lemma lem6779212 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : False.
Proof. exact (EQ_MP (@lem6779211 A K _88612 k f dom neut h1 h2) (@lem6778141 A K _88612 k f dom neut h2)). Qed.
Lemma lem6779213 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : (term622 A K _88612 k f dom neut) = False.
Proof. exact (prop_ext (fun h3 : term622 A K _88612 k f dom neut => @lem6779212 A K _88612 k f dom neut h1 h2) (fun h3 : False => @lem6777751 A K _88612 k f dom neut h2)). Qed.
Lemma lem6779214 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : False.
Proof. exact (EQ_MP (@lem6779213 A K _88612 k f dom neut h1 h2) (@lem6777751 A K _88612 k f dom neut h2)). Qed.
Lemma lem6779215 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : (term622 A K _88612 k f dom neut) = False.
Proof. exact (prop_ext (fun h3 : term622 A K _88612 k f dom neut => @lem6779214 A K _88612 k f dom neut h1 h2) (fun h3 : False => @lem6777751 A K _88612 k f dom neut h2)). Qed.
Lemma lem6779216 {A K : Type'} (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term85 A K _88612 k f dom neut) (h2 : term622 A K _88612 k f dom neut) : False.
Proof. exact (EQ_MP (@lem6779215 A K _88612 k f dom neut h1 h2) (@lem6777751 A K _88612 k f dom neut h2)). Qed.
Lemma lem6779217 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term621 A K ltle k f dom neut j i) : False.
Proof. exact (or_elim (@lem6777619 A K ltle k f dom neut j i h2) (fun h0 : term619 K k ltle j i => @lem6778738 K k ltle j i h1 h0) (fun h0 : term614 A K ltle k f dom neut j i => @lem6779210 A K ltle k f dom neut j i h1 h0)). Qed.
Lemma lem6779218 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term85 A K _88612 k f dom neut) (h3 : term568 A K _88612 ltle k f dom neut j i) : False.
Proof. exact (or_elim (@lem6777149 A K _88612 ltle k f dom neut j i h3) (fun h0 : term622 A K _88612 k f dom neut => @lem6779216 A K _88612 k f dom neut h2 h0) (fun h0 : term621 A K ltle k f dom neut j i => @lem6779217 A K ltle k f dom neut j i h1 h0)). Qed.
Lemma lem6779219 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (j : K) (i : K) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) (h4 : term568 A K _88612 ltle k f dom neut j i) : False.
Proof. exact (ex_elim (@lem6776509 A K _88612 h2) (fun i' : type848 A K => fun h0 : term493 A K _88612 i' => @lem6779218 A K _88612 ltle k f dom neut j i h1 h3 h4)). Qed.
Lemma lem6779220 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) (h4 : term193 A K _88612 ltle k f dom neut i) : False.
Proof. exact (ex_elim (@lem6776797 A K _88612 ltle k f dom neut i h4) (fun j : K => fun h0 : term570 A K _88612 ltle k f dom neut i j => @lem6779219 A K _88612 ltle k f dom neut j i h1 h2 h3 h0)). Qed.
Lemma lem6779221 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) (h4 : term193 A K _88612 ltle k f dom neut i) : (term85 A K _88612 k f dom neut) = False.
Proof. exact (prop_ext (fun h5 : term85 A K _88612 k f dom neut => @lem6779220 A K _88612 ltle k f dom neut i h1 h2 h3 h4) (fun h5 : False => @lem6776515 A K _88612 k f dom neut h3)). Qed.
Lemma lem6779222 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) (h4 : term193 A K _88612 ltle k f dom neut i) : False.
Proof. exact (EQ_MP (@lem6779221 A K _88612 ltle k f dom neut i h1 h2 h3 h4) (@lem6776515 A K _88612 k f dom neut h3)). Qed.
Lemma lem6779223 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) (h4 : term193 A K _88612 ltle k f dom neut i) : (term193 A K _88612 ltle k f dom neut i) = False.
Proof. exact (prop_ext (fun h5 : term193 A K _88612 ltle k f dom neut i => @lem6779222 A K _88612 ltle k f dom neut i h1 h2 h3 h4) (fun h5 : False => @lem6775483 A K _88612 ltle k f dom neut i h4)). Qed.
Lemma lem6779224 {A K : Type'} (_88612 : type849 A K) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) (h4 : term193 A K _88612 ltle k f dom neut i) : False.
Proof. exact (EQ_MP (@lem6779223 A K _88612 ltle k f dom neut i h1 h2 h3 h4) (@lem6775483 A K _88612 ltle k f dom neut i h4)). Qed.
Lemma lem6779225 {A K : Type'} (ltle : type1402 K) (i : K) (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) : term192 A K _88612 ltle k f dom neut i.
Proof. exact (fun h0 : term193 A K _88612 ltle k f dom neut i => @lem6779224 A K _88612 ltle k f dom neut i h1 h2 h3 h0). Qed.
Lemma lem6779226 {A K : Type'} (ltle : type1402 K) (i : K) (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term185 A K _88612) (h3 : term85 A K _88612 k f dom neut) : term88 A K _88612 ltle k f dom neut i.
Proof. exact (EQ_MP (@lem6775482 A K _88612 ltle k f dom neut i) (@lem6779225 A K ltle i _88612 k f dom neut h1 h2 h3)). Qed.
Lemma lem6779227 {A K : Type'} (ltle : type1402 K) (i : K) (_88612 : type849 A K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term185 A K _88612) (h2 : term85 A K _88612 k f dom neut) : term91 A K _88612 ltle k f dom neut i.
Proof. exact (fun h0 : term21 K k ltle i => @lem6779226 A K ltle i _88612 k f dom neut h0 h1 h2). Qed.
Lemma lem6779228 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : term185 A K _88612) : term93 A K _88612 ltle k f dom neut i.
Proof. exact (fun h0 : term85 A K _88612 k f dom neut => @lem6779227 A K ltle i _88612 k f dom neut h1 h0). Qed.
Lemma lem6779233 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : term185 A K _88612) : term95 A K _88612 k f dom neut i.
Proof. exact (fun ltle : type1402 K => @lem6779228 A K ltle k f dom neut i _88612 h1). Qed.
Lemma lem6779238 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : term185 A K _88612) : term97 A K _88612 f dom neut i.
Proof. exact (fun k : K -> Prop => @lem6779233 A K k f dom neut i _88612 h1). Qed.
Lemma lem6779243 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) (_88612 : type849 A K) (h1 : term185 A K _88612) : term99 A K _88612 dom neut i.
Proof. exact (fun f : K -> A => @lem6779238 A K f dom neut i _88612 h1). Qed.
Lemma lem6779248 {A K : Type'} (neut : A) (i : K) (_88612 : type849 A K) (h1 : term185 A K _88612) : term101 A K _88612 neut i.
Proof. exact (fun dom : A -> Prop => @lem6779243 A K dom neut i _88612 h1). Qed.
Lemma lem6779253 {A K : Type'} (i : K) (_88612 : type849 A K) (h1 : term185 A K _88612) : term103 A K _88612 i.
Proof. exact (fun neut : A => @lem6779248 A K neut i _88612 h1). Qed.
Lemma lem6779258 {A K : Type'} (_88612 : type849 A K) (h1 : term185 A K _88612) : term105 A K _88612.
Proof. exact (fun i : K => @lem6779253 A K i _88612 h1). Qed.
Lemma lem6779259 {A K : Type'} (_88612 : type849 A K) : term187 A K _88612.
Proof. exact (fun h0 : term185 A K _88612 => @lem6779258 A K _88612 h0). Qed.
Lemma lem6779264 {A K : Type'} : term189 A K.
Proof. exact (fun _88612 : type849 A K => @lem6779259 A K _88612). Qed.
Lemma lem6779265 {A K : Type'} : term60 A K.
Proof. exact (EQ_MP (@lem6775475 A K) (@lem6779264 A K)). Qed.
Lemma lem6779266 {A K : Type'} (i : K) : term652 A K i.
Proof. exact (@lem6779265 A K i). Qed.
Lemma lem6779267 {A K : Type'} (i : K) : (term652 A K i) = (term56 A K i).
Proof. exact (eq_refl (term652 A K i)). Qed.
Lemma lem6779268 {A K : Type'} (i : K) : term56 A K i.
Proof. exact (EQ_MP (@lem6779267 A K i) (@lem6779266 A K i)). Qed.
Lemma lem6779269 {A K : Type'} (i : K) (neut : A) : term653 A K i neut.
Proof. exact (@lem6779268 A K i neut). Qed.
Lemma lem6779270 {A K : Type'} (neut : A) (i : K) : (term653 A K i neut) = (term52 A K neut i).
Proof. exact (eq_refl (term653 A K i neut)). Qed.
Lemma lem6779271 {A K : Type'} (neut : A) (i : K) : term52 A K neut i.
Proof. exact (EQ_MP (@lem6779270 A K neut i) (@lem6779269 A K i neut)). Qed.
Lemma lem6779272 {A K : Type'} (neut : A) (i : K) (dom : A -> Prop) : term654 A K neut i dom.
Proof. exact (@lem6779271 A K neut i dom). Qed.
Lemma lem6779273 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) : (term654 A K neut i dom) = (term48 A K dom neut i).
Proof. exact (eq_refl (term654 A K neut i dom)). Qed.
Lemma lem6779274 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) : term48 A K dom neut i.
Proof. exact (EQ_MP (@lem6779273 A K dom neut i) (@lem6779272 A K neut i dom)). Qed.
Lemma lem6779275 {A K : Type'} (dom : A -> Prop) (neut : A) (i : K) (f : K -> A) : term655 A K dom neut i f.
Proof. exact (@lem6779274 A K dom neut i f). Qed.
Lemma lem6779276 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term655 A K dom neut i f) = (term44 A K f dom neut i).
Proof. exact (eq_refl (term655 A K dom neut i f)). Qed.
Lemma lem6779277 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term44 A K f dom neut i.
Proof. exact (EQ_MP (@lem6779276 A K f dom neut i) (@lem6779275 A K dom neut i f)). Qed.
Lemma lem6779278 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (k : K -> Prop) : term656 A K f dom neut i k.
Proof. exact (@lem6779277 A K f dom neut i k). Qed.
Lemma lem6779279 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term656 A K f dom neut i k) = (term40 A K k f dom neut i).
Proof. exact (eq_refl (term656 A K f dom neut i k)). Qed.
Lemma lem6779280 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term40 A K k f dom neut i.
Proof. exact (EQ_MP (@lem6779279 A K k f dom neut i) (@lem6779278 A K f dom neut i k)). Qed.
Lemma lem6779281 {A K : Type'} (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (ltle : type1402 K) : term657 A K k f dom neut i ltle.
Proof. exact (@lem6779280 A K k f dom neut i ltle). Qed.
Lemma lem6779282 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : (term657 A K k f dom neut i ltle) = (term27 A K ltle k f dom neut i).
Proof. exact (eq_refl (term657 A K k f dom neut i ltle)). Qed.
Lemma lem6779283 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term27 A K ltle k f dom neut i.
Proof. exact (EQ_MP (@lem6779282 A K ltle k f dom neut i) (@lem6779281 A K k f dom neut i ltle)). Qed.
Lemma lem6779285 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) : term27 A K ltle k f dom neut i.
Proof. exact (@lem6774788 A K ltle k f dom neut i (@lem6779283 A K ltle k f dom neut i)). Qed.
Lemma lem6779286 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term22 A K k f dom neut) : term34 A K ltle k f dom neut i.
Proof. exact (@lem6779285 A K ltle k f dom neut i (@lem6774738 A K k f dom neut h1)). Qed.
Lemma lem6779287 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : term25 A K ltle k f dom neut i.
Proof. exact (@lem6779286 A K ltle i k f dom neut h2 (@lem6774737 K k ltle i h1)). Qed.
Lemma lem6779288 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) (h3 : term26 A K ltle k f dom neut i) : False.
Proof. exact (@lem6779287 A K ltle i k f dom neut h1 h2 (@lem6774772 A K ltle k f dom neut i h3)). Qed.
Lemma lem6779289 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) (h3 : term26 A K ltle k f dom neut i) : (term26 A K ltle k f dom neut i) = False.
Proof. exact (prop_ext (fun h4 : term26 A K ltle k f dom neut i => @lem6779288 A K ltle k f dom neut i h1 h2 h3) (fun h4 : False => @lem6774772 A K ltle k f dom neut i h3)). Qed.
Lemma lem6779290 {A K : Type'} (ltle : type1402 K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (i : K) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) (h3 : term26 A K ltle k f dom neut i) : False.
Proof. exact (EQ_MP (@lem6779289 A K ltle k f dom neut i h1 h2 h3) (@lem6774772 A K ltle k f dom neut i h3)). Qed.
Lemma lem6779291 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : term25 A K ltle k f dom neut i.
Proof. exact (fun h0 : term26 A K ltle k f dom neut i => @lem6779290 A K ltle k f dom neut i h1 h2 h0). Qed.
Lemma lem6779292 {A K : Type'} (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : term15 A K ltle k f dom neut i.
Proof. exact (EQ_MP (@lem6774771 A K ltle k f dom neut i) (@lem6779291 A K ltle i k f dom neut h1 h2)). Qed.
Lemma lem6779294 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (@lem6774767 A K i dom neut op ltle k f (@lem6779292 A K ltle i k f dom neut h1 h2)). Qed.
Lemma lem6779295 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term20 A K f dom neut k ltle i) : term21 K k ltle i.
Proof. exact (proj2 (@lem6774736 A K f dom neut k ltle i h1)). Qed.
Lemma lem6779296 {A K : Type'} (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term20 A K f dom neut k ltle i) : term22 A K k f dom neut.
Proof. exact (proj1 (@lem6774736 A K f dom neut k ltle i h1)). Qed.
Lemma lem6779297 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : (term21 K k ltle i) = ((term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f)).
Proof. exact (prop_ext (fun h3 : term21 K k ltle i => @lem6779294 A K op ltle i k f dom neut h1 h2) (fun h3 : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f) => @lem6774737 K k ltle i h1)). Qed.
Lemma lem6779298 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (EQ_MP (@lem6779297 A K op ltle i k f dom neut h1 h2) (@lem6774737 K k ltle i h1)). Qed.
Lemma lem6779299 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : (term22 A K k f dom neut) = ((term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f)).
Proof. exact (prop_ext (fun h3 : term22 A K k f dom neut => @lem6779298 A K op ltle i k f dom neut h1 h2) (fun h3 : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f) => @lem6774738 A K k f dom neut h2)). Qed.
Lemma lem6779300 {A K : Type'} (op : type1400 A) (ltle : type1402 K) (i : K) (k : K -> Prop) (f : K -> A) (dom : A -> Prop) (neut : A) (h1 : term21 K k ltle i) (h2 : term22 A K k f dom neut) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (EQ_MP (@lem6779299 A K op ltle i k f dom neut h1 h2) (@lem6774738 A K k f dom neut h2)). Qed.
Lemma lem6779301 {A K : Type'} (op : type1400 A) (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term22 A K k f dom neut) (h2 : term20 A K f dom neut k ltle i) : (term21 K k ltle i) = ((term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f)).
Proof. exact (prop_ext (fun h3 : term21 K k ltle i => @lem6779300 A K op ltle i k f dom neut h3 h1) (fun h3 : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f) => @lem6779295 A K f dom neut k ltle i h2)). Qed.
Lemma lem6779302 {A K : Type'} (op : type1400 A) (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term22 A K k f dom neut) (h2 : term20 A K f dom neut k ltle i) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (EQ_MP (@lem6779301 A K op f dom neut k ltle i h1 h2) (@lem6779295 A K f dom neut k ltle i h2)). Qed.
Lemma lem6779303 {A K : Type'} (op : type1400 A) (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term20 A K f dom neut k ltle i) : (term22 A K k f dom neut) = ((term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f)).
Proof. exact (prop_ext (fun h2 : term22 A K k f dom neut => @lem6779302 A K op f dom neut k ltle i h2 h1) (fun h2 : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f) => @lem6779296 A K f dom neut k ltle i h1)). Qed.
Lemma lem6779304 {A K : Type'} (op : type1400 A) (f : K -> A) (dom : A -> Prop) (neut : A) (k : K -> Prop) (ltle : type1402 K) (i : K) (h1 : term20 A K f dom neut k ltle i) : (term16 A K dom neut op ltle i k f) = (term17 A K i dom neut op ltle k f).
Proof. exact (EQ_MP (@lem6779303 A K op f dom neut k ltle i h1) (@lem6779296 A K f dom neut k ltle i h1)). Qed.
Lemma lem6779305 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (k : K -> Prop) (f : K -> A) : term658 A K i dom neut op ltle k f.
Proof. exact (fun h0 : term20 A K f dom neut k ltle i => @lem6779304 A K op f dom neut k ltle i h0). Qed.
Lemma lem6779310 {A K : Type'} (i : K) (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term659 A K i dom neut op ltle f.
Proof. exact (fun k : K -> Prop => @lem6779305 A K i dom neut op ltle k f). Qed.
Lemma lem6779315 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term660 A K dom neut op ltle f.
Proof. exact (fun i : K => @lem6779310 A K i dom neut op ltle f). Qed.
Lemma lem6779316 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) (f : K -> A) : term661 A K dom neut op ltle f.
Proof. exact (conj (@lem6774754 A K dom op ltle f neut) (@lem6779315 A K dom neut op ltle f)). Qed.
Lemma lem6779321 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) (ltle : type1402 K) : term662 A K dom neut op ltle.
Proof. exact (fun f : K -> A => @lem6779316 A K dom neut op ltle f). Qed.
Lemma lem6779326 {A K : Type'} (dom : A -> Prop) (neut : A) (op : type1400 A) : term663 A K dom neut op.
Proof. exact (fun ltle : type1402 K => @lem6779321 A K dom neut op ltle). Qed.
Lemma lem6779331 {A K : Type'} (dom : A -> Prop) (neut : A) : term664 A K dom neut.
Proof. exact (fun op : type1400 A => @lem6779326 A K dom neut op). Qed.
Lemma lem6779336 {A K : Type'} (dom : A -> Prop) : term665 A K dom.
Proof. exact (fun neut : A => @lem6779331 A K dom neut). Qed.
Lemma lem6779341 {A K : Type'} : term666 A K.
Proof. exact (fun dom : A -> Prop => @lem6779336 A K dom). Qed.
