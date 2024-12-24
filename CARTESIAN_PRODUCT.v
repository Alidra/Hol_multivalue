Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARTESIAN_PRODUCT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSION_spec.
Require Import EXTENSIONAL_spec.
Require Import IN_SING_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm69_spec.
Lemma lem4399604 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4399605 {A B : Type'} (s : A -> Prop) : (term0 A B s) = ((@EXTENSIONAL A B s) = (term1 A B s)).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4399617 {_83152 : Type'} : term2 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4399618 {_83152 : Type'} (p : _83152 -> Prop) : term3 _83152 p.
Proof. exact (@lem4399617 _83152 p). Qed.
Lemma lem4399619 {_83152 : Type'} (p : _83152 -> Prop) : (term3 _83152 p) = (term4 _83152 p).
Proof. exact (eq_refl (term3 _83152 p)). Qed.
Lemma lem4399620 {_83152 : Type'} (p : _83152 -> Prop) : term4 _83152 p.
Proof. exact (EQ_MP (@lem4399619 _83152 p) (@lem4399618 _83152 p)). Qed.
Lemma lem4399621 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term5 _83152 p x.
Proof. exact (@lem4399620 _83152 p x). Qed.
Lemma lem4399622 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term5 _83152 p x) = ((term6 _83152 p x) = (p x)).
Proof. exact (eq_refl (term5 _83152 p x)). Qed.
Lemma lem4399631 {_83095 : Type'} : term7 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4399632 {_83095 : Type'} (p : _83095 -> Prop) : term8 _83095 p.
Proof. exact (@lem4399631 _83095 p). Qed.
Lemma lem4399633 {_83095 : Type'} (p : _83095 -> Prop) : (term8 _83095 p) = (term9 _83095 p).
Proof. exact (eq_refl (term8 _83095 p)). Qed.
Lemma lem4399634 {_83095 : Type'} (p : _83095 -> Prop) : term9 _83095 p.
Proof. exact (EQ_MP (@lem4399633 _83095 p) (@lem4399632 _83095 p)). Qed.
Lemma lem4399635 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term10 _83095 p x.
Proof. exact (@lem4399634 _83095 p x). Qed.
Lemma lem4399636 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term10 _83095 p x) = ((term11 _83095 x p) = (p x)).
Proof. exact (eq_refl (term10 _83095 p x)). Qed.
Lemma lem4399645 {A K : Type'} (k : K -> Prop) : term12 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4399646 {A K : Type'} (k : K -> Prop) : (term12 A K k) = (term13 A K k).
Proof. exact (eq_refl (term12 A K k)). Qed.
Lemma lem4399647 {A K : Type'} (k : K -> Prop) : term13 A K k.
Proof. exact (EQ_MP (@lem4399646 A K k) (@lem4399645 A K k)). Qed.
Lemma lem4399648 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term14 A K k s.
Proof. exact (@lem4399647 A K k s). Qed.
Lemma lem4399649 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term14 A K k s) = ((@cartesian_product A K k s) = (term15 A K k s)).
Proof. exact (eq_refl (term14 A K k s)). Qed.
Lemma lem4399651 {A : Type'} (s : A -> Prop) : term16 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4399652 {A : Type'} (s : A -> Prop) : (term16 A s) = (term17 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem4399653 {A : Type'} (s : A -> Prop) : term17 A s.
Proof. exact (EQ_MP (@lem4399652 A s) (@lem4399651 A s)). Qed.
Lemma lem4399654 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term18 A s t.
Proof. exact (@lem4399653 A s t). Qed.
Lemma lem4399655 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term18 A s t) = ((s = t) = (term19 A s t)).
Proof. exact (eq_refl (term18 A s t)). Qed.
Lemma lem4399658 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term19 A s t).
Proof. exact (EQ_MP (@lem4399655 A s t) (@lem4399654 A s t)). Qed.
Lemma lem4399659 {A K : Type'} (s : type805 A K) (t : type805 A K) : (s = t) = (term20 A K s t).
Proof. exact (@lem4399658 (K -> A) s t). Qed.
Lemma lem4399660 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : ((@cartesian_product A K k s) = (term21 A K k s)) = (term22 A K k s).
Proof. exact (@lem4399659 A K (@cartesian_product A K k s) (term21 A K k s)). Qed.
Lemma lem4399661 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = ((@cartesian_product A K k s) = (term21 A K k s)).
Proof. exact (SYM (@lem4399660 A K k s)). Qed.
Lemma lem4399669 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (EQ_MP (@lem4399649 A K k s) (@lem4399648 A K k s)). Qed.
Lemma lem4399670 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (@lem4399669 A K k s). Qed.
Lemma lem4399678 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term1 A B s).
Proof. exact (EQ_MP (@lem4399605 A B s) (@lem4399604 A B s)). Qed.
Lemma lem4399679 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term23 A K s).
Proof. exact (@lem4399678 K A s). Qed.
Lemma lem4399680 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term23 A K k).
Proof. exact (@lem4399679 A K k). Qed.
Lemma lem4399693 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399694 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term24 A K k f).
Proof. exact (MK_COMB (@lem4399680 A K k) (@lem4399693 A K f)). Qed.
Lemma lem4399696 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term6 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4399622 _83152 p x) (@lem4399621 _83152 p x)). Qed.
Lemma lem4399697 {A K : Type'} (p : type805 A K) (x : K -> A) : (term25 A K p x) = (p x).
Proof. exact (@lem4399696 (K -> A) p x). Qed.
Lemma lem4399698 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term26 A K k f) = (term27 A K k f).
Proof. exact (@lem4399697 A K (term28 A K k) f). Qed.
Lemma lem4399699 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term27 A K k f) = (term29 A K k f).
Proof. exact (eq_refl (term27 A K k f)). Qed.
Lemma lem4399700 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4399701 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term30 A K GEN_PVAR_139 k f) = (term31 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4399700 A K GEN_PVAR_139) (@lem4399699 A K k f)). Qed.
Lemma lem4399702 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399703 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term32 A K GEN_PVAR_139 k f) = (term33 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4399701 A K GEN_PVAR_139 k f) (@lem4399702 A K f)). Qed.
Lemma lem4399704 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term34 A K GEN_PVAR_139 k) = (term35 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4399703 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4399705 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4399706 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term36 A K GEN_PVAR_139 k) = (term37 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4399705 A K) (@lem4399704 A K GEN_PVAR_139 k)). Qed.
Lemma lem4399707 {A K : Type'} (k : K -> Prop) : (term38 A K k) = (term39 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4399706 A K GEN_PVAR_139 k)). Qed.
Lemma lem4399708 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4399709 {A K : Type'} (k : K -> Prop) : (term40 A K k) = (term23 A K k).
Proof. exact (MK_COMB (@lem4399708 A K) (@lem4399707 A K k)). Qed.
Lemma lem4399710 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399711 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term26 A K k f) = (term24 A K k f).
Proof. exact (MK_COMB (@lem4399709 A K k) (@lem4399710 A K f)). Qed.
Lemma lem4399712 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4399713 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term41 A K k f) = (term42 A K k f).
Proof. exact (MK_COMB (@lem4399712) (@lem4399711 A K k f)). Qed.
Lemma lem4399714 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term27 A K k f) = (term29 A K k f).
Proof. exact (eq_refl (term27 A K k f)). Qed.
Lemma lem4399715 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term26 A K k f) = (term27 A K k f)) = ((term24 A K k f) = (term29 A K k f)).
Proof. exact (MK_COMB (@lem4399713 A K k f) (@lem4399714 A K k f)). Qed.
Lemma lem4399716 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term24 A K k f) = (term29 A K k f).
Proof. exact (EQ_MP (@lem4399715 A K k f) (@lem4399698 A K k f)). Qed.
Lemma lem4399725 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term29 A K k f).
Proof. exact (TRANS (@lem4399694 A K k f) (@lem4399716 A K k f)). Qed.
Lemma lem4399726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4399727 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term43 A K k f) = (term44 A K k f).
Proof. exact (MK_COMB (@lem4399726) (@lem4399725 A K k f)). Qed.
Lemma lem4399734 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term45 A K k f s) = (term45 A K k f s).
Proof. exact (eq_refl (term45 A K k f s)). Qed.
Lemma lem4399735 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term46 A K k f s) = (term47 A K k f s).
Proof. exact (MK_COMB (@lem4399727 A K k f) (@lem4399734 A K k f s)). Qed.
Lemma lem4399738 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4399739 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term48 A K GEN_PVAR_140 k f s) = (term49 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4399738 A K GEN_PVAR_140) (@lem4399735 A K k f s)). Qed.
Lemma lem4399740 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399741 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term50 A K GEN_PVAR_140 k s f) = (term51 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4399739 A K GEN_PVAR_140 k f s) (@lem4399740 A K f)). Qed.
Lemma lem4399742 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term52 A K GEN_PVAR_140 k s) = (term53 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4399741 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4399743 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4399744 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term54 A K GEN_PVAR_140 k s) = (term55 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4399743 A K) (@lem4399742 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4399749 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term56 A K k s) = (term57 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4399744 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4399750 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4399751 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term15 A K k s) = (term58 A K k s).
Proof. exact (MK_COMB (@lem4399750 A K) (@lem4399749 A K k s)). Qed.
Lemma lem4399752 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term58 A K k s).
Proof. exact (TRANS (@lem4399670 A K k s) (@lem4399751 A K k s)). Qed.
Lemma lem4399753 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4399754 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term59 A K x k s) = (term60 A K x k s).
Proof. exact (MK_COMB (@lem4399753 A K x) (@lem4399752 A K k s)). Qed.
Lemma lem4399756 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4399636 _83095 p x) (@lem4399635 _83095 p x)). Qed.
Lemma lem4399757 {A K : Type'} (p : type805 A K) (x : K -> A) : (term61 A K x p) = (p x).
Proof. exact (@lem4399756 (K -> A) p x). Qed.
Lemma lem4399758 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term62 A K x k s) = (term63 A K k s x).
Proof. exact (@lem4399757 A K (term64 A K k s) x). Qed.
Lemma lem4399759 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term63 A K k s f) = (term47 A K k f s).
Proof. exact (eq_refl (term63 A K k s f)). Qed.
Lemma lem4399760 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4399761 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term65 A K GEN_PVAR_140 k s f) = (term49 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4399760 A K GEN_PVAR_140) (@lem4399759 A K k f s)). Qed.
Lemma lem4399762 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399763 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term66 A K GEN_PVAR_140 k s f) = (term51 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4399761 A K GEN_PVAR_140 k f s) (@lem4399762 A K f)). Qed.
Lemma lem4399764 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term67 A K GEN_PVAR_140 k s) = (term53 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4399763 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4399765 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4399766 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term68 A K GEN_PVAR_140 k s) = (term55 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4399765 A K) (@lem4399764 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4399767 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term69 A K k s) = (term57 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4399766 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4399768 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4399769 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term70 A K k s) = (term58 A K k s).
Proof. exact (MK_COMB (@lem4399768 A K) (@lem4399767 A K k s)). Qed.
Lemma lem4399770 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4399771 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term62 A K x k s) = (term60 A K x k s).
Proof. exact (MK_COMB (@lem4399770 A K x) (@lem4399769 A K k s)). Qed.
Lemma lem4399772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4399773 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term71 A K x k s) = (term72 A K x k s).
Proof. exact (MK_COMB (@lem4399772) (@lem4399771 A K x k s)). Qed.
Lemma lem4399774 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term63 A K k s x) = (term47 A K k x s).
Proof. exact (eq_refl (term63 A K k s x)). Qed.
Lemma lem4399775 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term62 A K x k s) = (term63 A K k s x)) = ((term60 A K x k s) = (term47 A K k x s)).
Proof. exact (MK_COMB (@lem4399773 A K x k s) (@lem4399774 A K k x s)). Qed.
Lemma lem4399776 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term60 A K x k s) = (term47 A K k x s).
Proof. exact (EQ_MP (@lem4399775 A K k x s) (@lem4399758 A K k s x)). Qed.
Lemma lem4399793 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term59 A K x k s) = (term47 A K k x s).
Proof. exact (TRANS (@lem4399754 A K x k s) (@lem4399776 A K k x s)). Qed.
Lemma lem4399794 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4399795 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term73 A K x k s) = (term74 A K k x s).
Proof. exact (MK_COMB (@lem4399794) (@lem4399793 A K k x s)). Qed.
Lemma lem4399797 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term11 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4399636 _83095 p x) (@lem4399635 _83095 p x)). Qed.
Lemma lem4399798 {A K : Type'} (p : type805 A K) (x : K -> A) : (term61 A K x p) = (p x).
Proof. exact (@lem4399797 (K -> A) p x). Qed.
Lemma lem4399799 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) : (term75 A K x k s) = (term76 A K k s x).
Proof. exact (@lem4399798 A K (term77 A K k s) x). Qed.
Lemma lem4399800 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term76 A K k s f) = (term78 A K f k s).
Proof. exact (eq_refl (term76 A K k s f)). Qed.
Lemma lem4399801 {A K : Type'} (GEN_PVAR_141 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_141) = (@SETSPEC (K -> A) GEN_PVAR_141).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_141)). Qed.
Lemma lem4399802 {A K : Type'} (GEN_PVAR_141 : K -> A) (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term79 A K GEN_PVAR_141 k s f) = (term80 A K GEN_PVAR_141 f k s).
Proof. exact (MK_COMB (@lem4399801 A K GEN_PVAR_141) (@lem4399800 A K f k s)). Qed.
Lemma lem4399803 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4399804 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term81 A K GEN_PVAR_141 k s f) = (term82 A K GEN_PVAR_141 k s f).
Proof. exact (MK_COMB (@lem4399802 A K GEN_PVAR_141 f k s) (@lem4399803 A K f)). Qed.
Lemma lem4399805 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term83 A K GEN_PVAR_141 k s) = (term84 A K GEN_PVAR_141 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4399804 A K GEN_PVAR_141 k s f)). Qed.
Lemma lem4399806 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4399807 {A K : Type'} (GEN_PVAR_141 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term85 A K GEN_PVAR_141 k s) = (term86 A K GEN_PVAR_141 k s).
Proof. exact (MK_COMB (@lem4399806 A K) (@lem4399805 A K GEN_PVAR_141 k s)). Qed.
Lemma lem4399808 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term87 A K k s) = (term88 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_141 : K -> A => @lem4399807 A K GEN_PVAR_141 k s)). Qed.
Lemma lem4399809 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4399810 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term89 A K k s) = (term21 A K k s).
Proof. exact (MK_COMB (@lem4399809 A K) (@lem4399808 A K k s)). Qed.
Lemma lem4399811 {A K : Type'} (x : K -> A) : (@IN (K -> A) x) = (@IN (K -> A) x).
Proof. exact (eq_refl (@IN (K -> A) x)). Qed.
Lemma lem4399812 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term75 A K x k s) = (term90 A K x k s).
Proof. exact (MK_COMB (@lem4399811 A K x) (@lem4399810 A K k s)). Qed.
Lemma lem4399813 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4399814 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term91 A K x k s) = (term92 A K x k s).
Proof. exact (MK_COMB (@lem4399813) (@lem4399812 A K x k s)). Qed.
Lemma lem4399815 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term76 A K k s x) = (term78 A K x k s).
Proof. exact (eq_refl (term76 A K k s x)). Qed.
Lemma lem4399816 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : ((term75 A K x k s) = (term76 A K k s x)) = ((term90 A K x k s) = (term78 A K x k s)).
Proof. exact (MK_COMB (@lem4399814 A K x k s) (@lem4399815 A K x k s)). Qed.
Lemma lem4399817 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : (term90 A K x k s) = (term78 A K x k s).
Proof. exact (EQ_MP (@lem4399816 A K x k s) (@lem4399799 A K k s x)). Qed.
Lemma lem4399822 {A K : Type'} (x : K -> A) (k : K -> Prop) (s : type1470 A K) : ((term59 A K x k s) = (term90 A K x k s)) = ((term47 A K k x s) = (term78 A K x k s)).
Proof. exact (MK_COMB (@lem4399795 A K k x s) (@lem4399817 A K x k s)). Qed.
Lemma lem4399825 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term93 A K k s) = (term94 A K k s).
Proof. exact (fun_ext (fun x : K -> A => @lem4399822 A K x k s)). Qed.
Lemma lem4399826 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4399827 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term22 A K k s) = (term95 A K k s).
Proof. exact (MK_COMB (@lem4399826 A K) (@lem4399825 A K k s)). Qed.
Lemma lem4399832 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term95 A K k s) = (term22 A K k s).
Proof. exact (SYM (@lem4399827 A K k s)). Qed.
Lemma lem4399834 (p : Prop) : p = (term96 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4399835 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term95 A K k s) = (term97 A K k s).
Proof. exact (@lem4399834 (term95 A K k s)). Qed.
Lemma lem4399836 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term97 A K k s) = (term95 A K k s).
Proof. exact (SYM (@lem4399835 A K k s)). Qed.
Lemma lem4399837 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term98 A K k s) : term98 A K k s.
Proof. exact (h1). Qed.
Lemma lem4399838 {K : Type'} : term99 K.
Proof. exact (@lem3205876 K). Qed.
Lemma lem4399839 {A : Type'} : term99 A.
Proof. exact (@lem3205876 A). Qed.
Lemma lem4399845 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term100 A K k s) : term100 A K k s.
Proof. exact (h1). Qed.
Lemma lem4399846 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term101 A K k s.
Proof. exact (fun h0 : term100 A K k s => @lem4399845 A K k s h0). Qed.
Lemma lem4399847 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term101 A K k s) : term101 A K k s.
Proof. exact (h1). Qed.
Lemma lem4399848 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term100 A K k s) : term100 A K k s.
Proof. exact (h1). Qed.
Lemma lem4399849 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term100 A K k s) (h2 : term101 A K k s) : term100 A K k s.
Proof. exact (@lem4399847 A K k s h2 (@lem4399848 A K k s h1)). Qed.
Lemma lem4399850 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term100 A K k s) : term102 A K k s.
Proof. exact (fun h0 : term101 A K k s => @lem4399849 A K k s h1 h0). Qed.
Lemma lem4399851 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term101 A K k s) : term101 A K k s.
Proof. exact (h1). Qed.
Lemma lem4399852 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term100 A K k s) (h2 : term101 A K k s) : term100 A K k s.
Proof. exact (@lem4399850 A K k s h1 (@lem4399851 A K k s h2)). Qed.
Lemma lem4399853 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term101 A K k s) : term101 A K k s.
Proof. exact (fun h0 : term100 A K k s => @lem4399852 A K k s h0 h1). Qed.
Lemma lem4399854 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term103 A K k s.
Proof. exact (fun h0 : term101 A K k s => @lem4399853 A K k s h0). Qed.
Lemma lem4399857 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term101 A K k s.
Proof. exact (@lem4399854 A K k s (@lem4399846 A K k s)). Qed.
Lemma lem4399858 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term101 A K k s.
Proof. exact (@lem4399857 A K k s). Qed.
Lemma lem4399902 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4399903 {K : Type'} : (term104 K) = (term105 K).
Proof. exact (@lem4399902 (term99 K)). Qed.
Lemma lem4399912 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (eq_refl (term106 A)). Qed.
Lemma lem4399913 {A K : Type'} : (term107 A K) = (term108 A K).
Proof. exact (MK_COMB (@lem4399912 A) (@lem4399903 K)). Qed.
Lemma lem4399916 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term109 A K k s) = (term109 A K k s).
Proof. exact (eq_refl (term109 A K k s)). Qed.
Lemma lem4399917 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term100 A K k s) = (term110 A K k s).
Proof. exact (MK_COMB (@lem4399916 A K k s) (@lem4399913 A K)). Qed.
Lemma lem4399920 {A K : Type'} (s : type1470 A K) : (term111 A K s) = (term112 A K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4399917 A K k s)). Qed.
Lemma lem4399921 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4399922 {A K : Type'} (s : type1470 A K) : (term113 A K s) = (term114 A K s).
Proof. exact (MK_COMB (@lem4399921 K) (@lem4399920 A K s)). Qed.
Lemma lem4399927 {A K : Type'} : (term115 A K) = (term116 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4399922 A K s)). Qed.
Lemma lem4399928 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4399937 {A K : Type'} : (term117 A K) = (term118 A K).
Proof. exact (MK_COMB (@lem4399928 A K) (@lem4399927 A K)). Qed.
Lemma lem4399942 {K : Type'} (x : K) (y : K) : ((term119 K x y) = (x = y)) = ((term119 K x y) = (x = y)).
Proof. exact (eq_refl ((term119 K x y) = (x = y))). Qed.
Lemma lem4399943 {K : Type'} (x : K) : (term120 K x) = (term120 K x).
Proof. exact (fun_ext (fun y : K => @lem4399942 K x y)). Qed.
Lemma lem4399944 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4399945 {K : Type'} (x : K) : (term121 K x) = (term121 K x).
Proof. exact (MK_COMB (@lem4399944 K) (@lem4399943 K x)). Qed.
Lemma lem4399946 {K : Type'} : (term122 K) = (term122 K).
Proof. exact (fun_ext (fun x : K => @lem4399945 K x)). Qed.
Lemma lem4399947 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4399948 {K : Type'} : (term99 K) = (term99 K).
Proof. exact (MK_COMB (@lem4399947 K) (@lem4399946 K)). Qed.
Lemma lem4399949 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4399950 {K : Type'} : (term105 K) = (term105 K).
Proof. exact (MK_COMB (@lem4399949) (@lem4399948 K)). Qed.
Lemma lem4399955 {A : Type'} (x : A) (y : A) : ((term119 A x y) = (x = y)) = ((term119 A x y) = (x = y)).
Proof. exact (eq_refl ((term119 A x y) = (x = y))). Qed.
Lemma lem4399956 {A : Type'} (x : A) : (term120 A x) = (term120 A x).
Proof. exact (fun_ext (fun y : A => @lem4399955 A x y)). Qed.
Lemma lem4399957 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4399958 {A : Type'} (x : A) : (term121 A x) = (term121 A x).
Proof. exact (MK_COMB (@lem4399957 A) (@lem4399956 A x)). Qed.
Lemma lem4399959 {A : Type'} : (term122 A) = (term122 A).
Proof. exact (fun_ext (fun x : A => @lem4399958 A x)). Qed.
Lemma lem4399960 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4399961 {A : Type'} : (term99 A) = (term99 A).
Proof. exact (MK_COMB (@lem4399960 A) (@lem4399959 A)). Qed.
Lemma lem4399962 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4399963 {A : Type'} : (term106 A) = (term106 A).
Proof. exact (MK_COMB (@lem4399962) (@lem4399961 A)). Qed.
Lemma lem4399964 {A K : Type'} : (term108 A K) = (term108 A K).
Proof. exact (MK_COMB (@lem4399963 A) (@lem4399950 K)). Qed.
Lemma lem4399968 {K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (@IN K i k) = False.
Proof. exact (h1). Qed.
Lemma lem4399969 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4399970 {A K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term123 A K i k) = (@COND (A -> Prop) False).
Proof. exact (MK_COMB (@lem4399969 A) (@lem4399968 K i k h1)). Qed.
Lemma lem4399971 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4399972 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term124 A K k s i) = (term125 A K s i).
Proof. exact (MK_COMB (@lem4399970 A K i k h1) (@lem4399971 A K s i)). Qed.
Lemma lem4399973 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4399974 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term126 A K k s i) = (term127 A K s i).
Proof. exact (MK_COMB (@lem4399972 A K s i k h1) (@lem4399973 A)). Qed.
Lemma lem4399976 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4399977 {A : Type'} (t1 : A -> Prop) (t2 : A -> Prop) : (@COND (A -> Prop) False t1 t2) = t2.
Proof. exact (@lem4399976 (A -> Prop) t1 t2). Qed.
Lemma lem4399978 {A K : Type'} (s : type1470 A K) (i : K) : (term127 A K s i) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (@lem4399977 A (s i) (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4399979 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term126 A K k s i) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (TRANS (@lem4399974 A K s i k h1) (@lem4399978 A K s i)). Qed.
Lemma lem4399980 {A K : Type'} (x : K -> A) (i : K) : (term128 A K x i) = (term128 A K x i).
Proof. exact (eq_refl (term128 A K x i)). Qed.
Lemma lem4399981 {A K : Type'} (s : type1470 A K) (x : K -> A) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = False) : (term129 A K x k s i) = (term130 A K x i).
Proof. exact (MK_COMB (@lem4399980 A K x i) (@lem4399979 A K s i k h1)). Qed.
Lemma lem4399982 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (x : K -> A) (i : K) : term131 A K k s x i.
Proof. exact (fun h0 : (@IN K i k) = False => @lem4399981 A K s x i k h0). Qed.
Lemma lem4399984 {K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (@IN K i k) = True.
Proof. exact (h1). Qed.
Lemma lem4399985 {A : Type'} : (@COND (A -> Prop)) = (@COND (A -> Prop)).
Proof. exact (eq_refl (@COND (A -> Prop))). Qed.
Lemma lem4399986 {A K : Type'} (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term123 A K i k) = (@COND (A -> Prop) True).
Proof. exact (MK_COMB (@lem4399985 A) (@lem4399984 K i k h1)). Qed.
Lemma lem4399987 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4399988 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term124 A K k s i) = (term132 A K s i).
Proof. exact (MK_COMB (@lem4399986 A K i k h1) (@lem4399987 A K s i)). Qed.
Lemma lem4399989 {A : Type'} : (@INSERT A (@ARB A) (@EMPTY A)) = (@INSERT A (@ARB A) (@EMPTY A)).
Proof. exact (eq_refl (@INSERT A (@ARB A) (@EMPTY A))). Qed.
Lemma lem4399990 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term126 A K k s i) = (term133 A K s i).
Proof. exact (MK_COMB (@lem4399988 A K s i k h1) (@lem4399989 A)). Qed.
Lemma lem4399992 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4399993 {A : Type'} (t2 : A -> Prop) (t1 : A -> Prop) : (@COND (A -> Prop) True t1 t2) = t1.
Proof. exact (@lem4399992 (A -> Prop) t2 t1). Qed.
Lemma lem4399994 {A K : Type'} (s : type1470 A K) (i : K) : (term133 A K s i) = (s i).
Proof. exact (@lem4399993 A (@INSERT A (@ARB A) (@EMPTY A)) (s i)). Qed.
Lemma lem4399995 {A K : Type'} (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term126 A K k s i) = (s i).
Proof. exact (TRANS (@lem4399990 A K s i k h1) (@lem4399994 A K s i)). Qed.
Lemma lem4399996 {A K : Type'} (x : K -> A) (i : K) : (term128 A K x i) = (term128 A K x i).
Proof. exact (eq_refl (term128 A K x i)). Qed.
Lemma lem4399997 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) (k : K -> Prop) (h1 : (@IN K i k) = True) : (term129 A K x k s i) = (term134 A K x s i).
Proof. exact (MK_COMB (@lem4399996 A K x i) (@lem4399995 A K s i k h1)). Qed.
Lemma lem4399998 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : term135 A K k x s i.
Proof. exact (fun h0 : (@IN K i k) = True => @lem4399997 A K x s i k h0). Qed.
Lemma lem4399999 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : term136 A K k x s i.
Proof. exact (conj (@lem4399982 A K k s x i) (@lem4399998 A K k x s i)). Qed.
Lemma lem4400001 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term137 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4400002 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : term138 A K s k x i.
Proof. exact (@lem4400001 (term129 A K x k s i) (term134 A K x s i) (@IN K i k) (term130 A K x i)). Qed.
Lemma lem4400035 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term129 A K x k s i) = (term139 A K s k x i).
Proof. exact (@lem4400002 A K s k x i (@lem4399999 A K k x s i)). Qed.
Lemma lem4400036 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term140 A K x k s) = (term141 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400035 A K s k x i)). Qed.
Lemma lem4400037 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400038 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term78 A K x k s) = (term142 A K s k x).
Proof. exact (MK_COMB (@lem4400037 K) (@lem4400036 A K s k x)). Qed.
Lemma lem4400043 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term143 A K k x s i) = (term143 A K k x s i).
Proof. exact (eq_refl (term143 A K k x s i)). Qed.
Lemma lem4400044 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term144 A K k x s) = (term144 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4400043 A K k x s i)). Qed.
Lemma lem4400045 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400046 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term45 A K k x s) = (term45 A K k x s).
Proof. exact (MK_COMB (@lem4400045 K) (@lem4400044 A K k x s)). Qed.
Lemma lem4400053 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term145 A K k x x') = (term145 A K k x x').
Proof. exact (eq_refl (term145 A K k x x')). Qed.
Lemma lem4400054 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term146 A K k x) = (term146 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4400053 A K k x x')). Qed.
Lemma lem4400055 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400056 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term29 A K k x) = (term29 A K k x).
Proof. exact (MK_COMB (@lem4400055 K) (@lem4400054 A K k x)). Qed.
Lemma lem4400057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400058 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term44 A K k x) = (term44 A K k x).
Proof. exact (MK_COMB (@lem4400057) (@lem4400056 A K k x)). Qed.
Lemma lem4400059 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term47 A K k x s) = (term47 A K k x s).
Proof. exact (MK_COMB (@lem4400058 A K k x) (@lem4400046 A K k x s)). Qed.
Lemma lem4400060 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4400061 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term74 A K k x s) = (term74 A K k x s).
Proof. exact (MK_COMB (@lem4400060) (@lem4400059 A K k x s)). Qed.
Lemma lem4400062 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term47 A K k x s) = (term78 A K x k s)) = ((term47 A K k x s) = (term142 A K s k x)).
Proof. exact (MK_COMB (@lem4400061 A K k x s) (@lem4400038 A K s k x)). Qed.
Lemma lem4400063 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term94 A K k s) = (term147 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400062 A K s k x)). Qed.
Lemma lem4400064 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4400065 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term95 A K k s) = (term148 A K s k).
Proof. exact (MK_COMB (@lem4400064 A K) (@lem4400063 A K s k)). Qed.
Lemma lem4400066 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4400067 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term98 A K k s) = (term149 A K s k).
Proof. exact (MK_COMB (@lem4400066) (@lem4400065 A K s k)). Qed.
Lemma lem4400068 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4400069 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term109 A K k s) = (term150 A K s k).
Proof. exact (MK_COMB (@lem4400068) (@lem4400067 A K s k)). Qed.
Lemma lem4400070 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term110 A K k s) = (term151 A K s k).
Proof. exact (MK_COMB (@lem4400069 A K s k) (@lem4399964 A K)). Qed.
Lemma lem4400071 {A K : Type'} (s : type1470 A K) : (term112 A K s) = (term152 A K s).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4400070 A K s k)). Qed.
Lemma lem4400072 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4400073 {A K : Type'} (s : type1470 A K) : (term114 A K s) = (term153 A K s).
Proof. exact (MK_COMB (@lem4400072 K) (@lem4400071 A K s)). Qed.
Lemma lem4400074 {A K : Type'} : (term116 A K) = (term154 A K).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4400073 A K s)). Qed.
Lemma lem4400075 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4400076 {A K : Type'} : (term118 A K) = (term155 A K).
Proof. exact (MK_COMB (@lem4400075 A K) (@lem4400074 A K)). Qed.
Lemma lem4400155 {A K : Type'} : (term117 A K) = (term155 A K).
Proof. exact (TRANS (@lem4399937 A K) (@lem4400076 A K)). Qed.
Lemma lem4400156 {A K : Type'} : (term155 A K) = (term117 A K).
Proof. exact (SYM (@lem4400155 A K)). Qed.
Lemma lem4400157 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (h1 : term149 A K s k) : term149 A K s k.
Proof. exact (h1). Qed.
Lemma lem4400158 {A : Type'} (h1 : term99 A) : term99 A.
Proof. exact (h1). Qed.
Lemma lem4400163 {K : Type'} (x : K) (k : K -> Prop) : (term156 K x k) = (@IN K x k).
Proof. exact (@lem16933 (@IN K x k)). Qed.
Lemma lem4400165 {A K : Type'} (x : K -> A) (x' : K) : ((x x') = (@ARB A)) = ((x x') = (@ARB A)).
Proof. exact (eq_refl ((x x') = (@ARB A))). Qed.
Lemma lem4400170 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term157 A K k x x') = (term158 A K k x x').
Proof. exact (@lem17362 (term159 K x' k) ((x x') = (@ARB A))). Qed.
Lemma lem4400171 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400172 {K : Type'} (x : K) (k : K -> Prop) : (term160 K x k) = (term161 K x k).
Proof. exact (MK_COMB (@lem4400171) (@lem4400163 K x k)). Qed.
Lemma lem4400173 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term162 A K k x x') = (term163 A K k x x').
Proof. exact (MK_COMB (@lem4400172 K x' k) (@lem4400165 A K x x')). Qed.
Lemma lem4400174 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term145 A K k x x') = (term162 A K k x x').
Proof. exact (@lem17265 (term159 K x' k) ((x x') = (@ARB A))). Qed.
Lemma lem4400175 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term145 A K k x x') = (term163 A K k x x').
Proof. exact (TRANS (@lem4400174 A K k x x') (@lem4400173 A K k x x')). Qed.
Lemma lem4400176 {K : Type'} (P : K -> Prop) : (term164 K P) = (term165 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4400177 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term166 A K k x) = (term167 A K k x).
Proof. exact (@lem4400176 K (term146 A K k x)). Qed.
Lemma lem4400178 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term168 A K k x x') = (term145 A K k x x').
Proof. exact (eq_refl (term168 A K k x x')). Qed.
Lemma lem4400179 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4400180 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term169 A K k x x') = (term157 A K k x x').
Proof. exact (MK_COMB (@lem4400179) (@lem4400178 A K k x x')). Qed.
Lemma lem4400181 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term169 A K k x x') = (term158 A K k x x').
Proof. exact (TRANS (@lem4400180 A K k x x') (@lem4400170 A K k x x')). Qed.
Lemma lem4400182 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term170 A K k x) = (term171 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4400181 A K k x x')). Qed.
Lemma lem4400183 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400184 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term167 A K k x) = (term172 A K k x).
Proof. exact (MK_COMB (@lem4400183 K) (@lem4400182 A K k x)). Qed.
Lemma lem4400185 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term166 A K k x) = (term172 A K k x).
Proof. exact (TRANS (@lem4400177 A K k x) (@lem4400184 A K k x)). Qed.
Lemma lem4400186 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term146 A K k x) = (term173 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4400175 A K k x x')). Qed.
Lemma lem4400187 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400188 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term29 A K k x) = (term174 A K k x).
Proof. exact (MK_COMB (@lem4400187 K) (@lem4400186 A K k x)). Qed.
Lemma lem4400197 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term175 A K k x s i) = (term176 A K k x s i).
Proof. exact (@lem17362 (@IN K i k) (term134 A K x s i)). Qed.
Lemma lem4400202 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term143 A K k x s i) = (term177 A K k x s i).
Proof. exact (@lem17265 (@IN K i k) (term134 A K x s i)). Qed.
Lemma lem4400203 {K : Type'} (P : K -> Prop) : (term164 K P) = (term165 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4400204 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term178 A K k x s) = (term179 A K k x s).
Proof. exact (@lem4400203 K (term144 A K k x s)). Qed.
Lemma lem4400205 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term180 A K k x s i) = (term143 A K k x s i).
Proof. exact (eq_refl (term180 A K k x s i)). Qed.
Lemma lem4400206 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4400207 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term181 A K k x s i) = (term175 A K k x s i).
Proof. exact (MK_COMB (@lem4400206) (@lem4400205 A K k x s i)). Qed.
Lemma lem4400208 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term181 A K k x s i) = (term176 A K k x s i).
Proof. exact (TRANS (@lem4400207 A K k x s i) (@lem4400197 A K k x s i)). Qed.
Lemma lem4400209 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term182 A K k x s) = (term183 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4400208 A K k x s i)). Qed.
Lemma lem4400210 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400211 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term179 A K k x s) = (term184 A K k x s).
Proof. exact (MK_COMB (@lem4400210 K) (@lem4400209 A K k x s)). Qed.
Lemma lem4400212 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term178 A K k x s) = (term184 A K k x s).
Proof. exact (TRANS (@lem4400204 A K k x s) (@lem4400211 A K k x s)). Qed.
Lemma lem4400213 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term144 A K k x s) = (term185 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4400202 A K k x s i)). Qed.
Lemma lem4400214 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400215 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term45 A K k x s) = (term186 A K k x s).
Proof. exact (MK_COMB (@lem4400214 K) (@lem4400213 A K k x s)). Qed.
Lemma lem4400216 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400217 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term187 A K k x) = (term188 A K k x).
Proof. exact (MK_COMB (@lem4400216) (@lem4400185 A K k x)). Qed.
Lemma lem4400218 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term189 A K k x s) = (term190 A K k x s).
Proof. exact (MK_COMB (@lem4400217 A K k x) (@lem4400212 A K k x s)). Qed.
Lemma lem4400219 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term191 A K k x s) = (term189 A K k x s).
Proof. exact (@lem17045 (term29 A K k x) (term45 A K k x s)). Qed.
Lemma lem4400220 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term191 A K k x s) = (term190 A K k x s).
Proof. exact (TRANS (@lem4400219 A K k x s) (@lem4400218 A K k x s)). Qed.
Lemma lem4400221 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400222 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term44 A K k x) = (term192 A K k x).
Proof. exact (MK_COMB (@lem4400221) (@lem4400188 A K k x)). Qed.
Lemma lem4400223 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term47 A K k x s) = (term193 A K k x s).
Proof. exact (MK_COMB (@lem4400222 A K k x) (@lem4400215 A K k x s)). Qed.
Lemma lem4400227 {K : Type'} (i : K) (k : K -> Prop) : (term156 K i k) = (@IN K i k).
Proof. exact (@lem16933 (@IN K i k)). Qed.
Lemma lem4400228 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term194 A K x s i) = (term194 A K x s i).
Proof. exact (eq_refl (term194 A K x s i)). Qed.
Lemma lem4400230 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400231 {K : Type'} (i : K) (k : K -> Prop) : (term195 K i k) = (term196 K i k).
Proof. exact (MK_COMB (@lem4400230) (@lem4400227 K i k)). Qed.
Lemma lem4400232 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term197 A K k x s i) = (term176 A K k x s i).
Proof. exact (MK_COMB (@lem4400231 K i k) (@lem4400228 A K x s i)). Qed.
Lemma lem4400233 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term198 A K k x s i) = (term197 A K k x s i).
Proof. exact (@lem17160 (term159 K i k) (term134 A K x s i)). Qed.
Lemma lem4400234 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term198 A K k x s i) = (term176 A K k x s i).
Proof. exact (TRANS (@lem4400233 A K k x s i) (@lem4400232 A K k x s i)). Qed.
Lemma lem4400246 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term199 A K k x i) = (term200 A K k x i).
Proof. exact (@lem17160 (@IN K i k) (term130 A K x i)). Qed.
Lemma lem4400250 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400251 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term201 A K k x s i) = (term202 A K k x s i).
Proof. exact (MK_COMB (@lem4400250) (@lem4400234 A K k x s i)). Qed.
Lemma lem4400252 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term203 A K s k x i) = (term204 A K s k x i).
Proof. exact (MK_COMB (@lem4400251 A K k x s i) (@lem4400246 A K k x i)). Qed.
Lemma lem4400253 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term205 A K s k x i) = (term203 A K s k x i).
Proof. exact (@lem17045 (term177 A K k x s i) (term206 A K k x i)). Qed.
Lemma lem4400254 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term205 A K s k x i) = (term204 A K s k x i).
Proof. exact (TRANS (@lem4400253 A K s k x i) (@lem4400252 A K s k x i)). Qed.
Lemma lem4400257 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term139 A K s k x i) = (term139 A K s k x i).
Proof. exact (eq_refl (term139 A K s k x i)). Qed.
Lemma lem4400258 {K : Type'} (P : K -> Prop) : (term164 K P) = (term165 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4400259 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term207 A K s k x) = (term208 A K s k x).
Proof. exact (@lem4400258 K (term141 A K s k x)). Qed.
Lemma lem4400260 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term209 A K s k x i) = (term139 A K s k x i).
Proof. exact (eq_refl (term209 A K s k x i)). Qed.
Lemma lem4400261 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4400262 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term210 A K s k x i) = (term205 A K s k x i).
Proof. exact (MK_COMB (@lem4400261) (@lem4400260 A K s k x i)). Qed.
Lemma lem4400263 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term210 A K s k x i) = (term204 A K s k x i).
Proof. exact (TRANS (@lem4400262 A K s k x i) (@lem4400254 A K s k x i)). Qed.
Lemma lem4400264 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term211 A K s k x) = (term212 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400263 A K s k x i)). Qed.
Lemma lem4400265 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400266 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term208 A K s k x) = (term213 A K s k x).
Proof. exact (MK_COMB (@lem4400265 K) (@lem4400264 A K s k x)). Qed.
Lemma lem4400267 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term207 A K s k x) = (term213 A K s k x).
Proof. exact (TRANS (@lem4400259 A K s k x) (@lem4400266 A K s k x)). Qed.
Lemma lem4400268 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term141 A K s k x) = (term141 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400257 A K s k x i)). Qed.
Lemma lem4400269 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400270 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term142 A K s k x) = (term142 A K s k x).
Proof. exact (MK_COMB (@lem4400269 K) (@lem4400268 A K s k x)). Qed.
Lemma lem4400271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400272 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term214 A K k x s) = (term215 A K k x s).
Proof. exact (MK_COMB (@lem4400271) (@lem4400220 A K k x s)). Qed.
Lemma lem4400273 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term216 A K s k x) = (term217 A K s k x).
Proof. exact (MK_COMB (@lem4400272 A K k x s) (@lem4400270 A K s k x)). Qed.
Lemma lem4400274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400275 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term218 A K k x s) = (term219 A K k x s).
Proof. exact (MK_COMB (@lem4400274) (@lem4400223 A K k x s)). Qed.
Lemma lem4400276 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term220 A K s k x) = (term221 A K s k x).
Proof. exact (MK_COMB (@lem4400275 A K k x s) (@lem4400267 A K s k x)). Qed.
Lemma lem4400277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400278 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term222 A K s k x) = (term223 A K s k x).
Proof. exact (MK_COMB (@lem4400277) (@lem4400276 A K s k x)). Qed.
Lemma lem4400279 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term224 A K s k x) = (term225 A K s k x).
Proof. exact (MK_COMB (@lem4400278 A K s k x) (@lem4400273 A K s k x)). Qed.
Lemma lem4400280 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term226 A K s k x) = (term224 A K s k x).
Proof. exact (@lem17646 (term47 A K k x s) (term142 A K s k x)). Qed.
Lemma lem4400281 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term226 A K s k x) = (term225 A K s k x).
Proof. exact (TRANS (@lem4400280 A K s k x) (@lem4400279 A K s k x)). Qed.
Lemma lem4400282 {A K : Type'} (P : type805 A K) : (term227 A K P) = (term228 A K P).
Proof. exact (@lem18392 (K -> A) P). Qed.
Lemma lem4400283 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term149 A K s k) = (term229 A K s k).
Proof. exact (@lem4400282 A K (term147 A K s k)). Qed.
Lemma lem4400284 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term230 A K s k x) = ((term47 A K k x s) = (term142 A K s k x)).
Proof. exact (eq_refl (term230 A K s k x)). Qed.
Lemma lem4400285 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4400286 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term231 A K s k x) = (term226 A K s k x).
Proof. exact (MK_COMB (@lem4400285) (@lem4400284 A K s k x)). Qed.
Lemma lem4400287 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term231 A K s k x) = (term225 A K s k x).
Proof. exact (TRANS (@lem4400286 A K s k x) (@lem4400281 A K s k x)). Qed.
Lemma lem4400288 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term232 A K s k) = (term233 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400287 A K s k x)). Qed.
Lemma lem4400289 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4400290 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term229 A K s k) = (term234 A K s k).
Proof. exact (MK_COMB (@lem4400289 A K) (@lem4400288 A K s k)). Qed.
Lemma lem4400291 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term149 A K s k) = (term234 A K s k).
Proof. exact (TRANS (@lem4400283 A K s k) (@lem4400290 A K s k)). Qed.
Lemma lem4400293 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4400294 {A K : Type'} (P : type805 A K) (Q : type805 A K) : (term237 A K P Q) = (term238 A K P Q).
Proof. exact (@lem4400293 (K -> A) P Q). Qed.
Lemma lem4400295 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term239 A K s k) = (term240 A K s k).
Proof. exact (@lem4400294 A K (term241 A K s k) (term242 A K s k)). Qed.
Lemma lem4400296 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term243 A K s k x) = (term221 A K s k x).
Proof. exact (eq_refl (term243 A K s k x)). Qed.
Lemma lem4400297 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400298 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term244 A K s k x) = (term223 A K s k x).
Proof. exact (MK_COMB (@lem4400297) (@lem4400296 A K s k x)). Qed.
Lemma lem4400299 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term245 A K s k x) = (term217 A K s k x).
Proof. exact (eq_refl (term245 A K s k x)). Qed.
Lemma lem4400300 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term246 A K s k x) = (term225 A K s k x).
Proof. exact (MK_COMB (@lem4400298 A K s k x) (@lem4400299 A K s k x)). Qed.
Lemma lem4400301 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term247 A K s k) = (term233 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400300 A K s k x)). Qed.
Lemma lem4400302 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4400303 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term239 A K s k) = (term234 A K s k).
Proof. exact (MK_COMB (@lem4400302 A K) (@lem4400301 A K s k)). Qed.
Lemma lem4400304 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4400305 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term248 A K s k) = (term249 A K s k).
Proof. exact (MK_COMB (@lem4400304) (@lem4400303 A K s k)). Qed.
Lemma lem4400306 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term243 A K s k x) = (term221 A K s k x).
Proof. exact (eq_refl (term243 A K s k x)). Qed.
Lemma lem4400307 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term250 A K s k) = (term241 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400306 A K s k x)). Qed.
Lemma lem4400308 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4400309 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term251 A K s k) = (term252 A K s k).
Proof. exact (MK_COMB (@lem4400308 A K) (@lem4400307 A K s k)). Qed.
Lemma lem4400310 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400311 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term253 A K s k) = (term254 A K s k).
Proof. exact (MK_COMB (@lem4400310) (@lem4400309 A K s k)). Qed.
Lemma lem4400312 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term245 A K s k x) = (term217 A K s k x).
Proof. exact (eq_refl (term245 A K s k x)). Qed.
Lemma lem4400313 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term255 A K s k) = (term242 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400312 A K s k x)). Qed.
Lemma lem4400314 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4400315 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term256 A K s k) = (term257 A K s k).
Proof. exact (MK_COMB (@lem4400314 A K) (@lem4400313 A K s k)). Qed.
Lemma lem4400316 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term240 A K s k) = (term258 A K s k).
Proof. exact (MK_COMB (@lem4400311 A K s k) (@lem4400315 A K s k)). Qed.
Lemma lem4400317 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : ((term239 A K s k) = (term240 A K s k)) = ((term234 A K s k) = (term258 A K s k)).
Proof. exact (MK_COMB (@lem4400305 A K s k) (@lem4400316 A K s k)). Qed.
Lemma lem4400318 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term234 A K s k) = (term258 A K s k).
Proof. exact (EQ_MP (@lem4400317 A K s k) (@lem4400295 A K s k)). Qed.
Lemma lem4400464 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term235 A P Q) = (term236 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem4400465 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term235 K P Q) = (term236 K P Q).
Proof. exact (@lem4400464 K P Q). Qed.
Lemma lem4400466 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term259 A K s k x) = (term260 A K s k x).
Proof. exact (@lem4400465 K (term183 A K k x s) (term261 A K k x)). Qed.
Lemma lem4400467 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term262 A K k x s i) = (term176 A K k x s i).
Proof. exact (eq_refl (term262 A K k x s i)). Qed.
Lemma lem4400468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400469 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term263 A K k x s i) = (term202 A K k x s i).
Proof. exact (MK_COMB (@lem4400468) (@lem4400467 A K k x s i)). Qed.
Lemma lem4400470 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term264 A K k x i) = (term200 A K k x i).
Proof. exact (eq_refl (term264 A K k x i)). Qed.
Lemma lem4400471 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term265 A K s k x i) = (term204 A K s k x i).
Proof. exact (MK_COMB (@lem4400469 A K k x s i) (@lem4400470 A K k x i)). Qed.
Lemma lem4400472 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term266 A K s k x) = (term212 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400471 A K s k x i)). Qed.
Lemma lem4400473 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400474 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term259 A K s k x) = (term213 A K s k x).
Proof. exact (MK_COMB (@lem4400473 K) (@lem4400472 A K s k x)). Qed.
Lemma lem4400475 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4400476 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term267 A K s k x) = (term268 A K s k x).
Proof. exact (MK_COMB (@lem4400475) (@lem4400474 A K s k x)). Qed.
Lemma lem4400477 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term262 A K k x s i) = (term176 A K k x s i).
Proof. exact (eq_refl (term262 A K k x s i)). Qed.
Lemma lem4400478 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term269 A K k x s) = (term183 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4400477 A K k x s i)). Qed.
Lemma lem4400479 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400480 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term270 A K k x s) = (term184 A K k x s).
Proof. exact (MK_COMB (@lem4400479 K) (@lem4400478 A K k x s)). Qed.
Lemma lem4400481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400482 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term271 A K k x s) = (term272 A K k x s).
Proof. exact (MK_COMB (@lem4400481) (@lem4400480 A K k x s)). Qed.
Lemma lem4400483 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term264 A K k x i) = (term200 A K k x i).
Proof. exact (eq_refl (term264 A K k x i)). Qed.
Lemma lem4400484 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term273 A K k x) = (term261 A K k x).
Proof. exact (fun_ext (fun i : K => @lem4400483 A K k x i)). Qed.
Lemma lem4400485 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400486 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term274 A K k x) = (term275 A K k x).
Proof. exact (MK_COMB (@lem4400485 K) (@lem4400484 A K k x)). Qed.
Lemma lem4400487 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term260 A K s k x) = (term276 A K s k x).
Proof. exact (MK_COMB (@lem4400482 A K k x s) (@lem4400486 A K k x)). Qed.
Lemma lem4400488 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term259 A K s k x) = (term260 A K s k x)) = ((term213 A K s k x) = (term276 A K s k x)).
Proof. exact (MK_COMB (@lem4400476 A K s k x) (@lem4400487 A K s k x)). Qed.
Lemma lem4400489 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term213 A K s k x) = (term276 A K s k x).
Proof. exact (EQ_MP (@lem4400488 A K s k x) (@lem4400466 A K s k x)). Qed.
Lemma lem4400586 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term219 A K k x s) = (term219 A K k x s).
Proof. exact (eq_refl (term219 A K k x s)). Qed.
Lemma lem4400587 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term221 A K s k x) = (term277 A K s k x).
Proof. exact (MK_COMB (@lem4400586 A K k x s) (@lem4400489 A K s k x)). Qed.
Lemma lem4400588 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term241 A K s k) = (term278 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400587 A K s k x)). Qed.
Lemma lem4400589 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4400590 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term252 A K s k) = (term279 A K s k).
Proof. exact (MK_COMB (@lem4400589 A K) (@lem4400588 A K s k)). Qed.
Lemma lem4400639 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400640 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term254 A K s k) = (term280 A K s k).
Proof. exact (MK_COMB (@lem4400639) (@lem4400590 A K s k)). Qed.
Lemma lem4400786 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4400787 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term281 K P Q) = (term282 K P Q).
Proof. exact (@lem4400786 K P Q). Qed.
Lemma lem4400788 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term283 A K s k x) = (term284 A K s k x).
Proof. exact (@lem4400787 K (term185 A K k x s) (term285 A K k x)). Qed.
Lemma lem4400789 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term286 A K k x s i) = (term177 A K k x s i).
Proof. exact (eq_refl (term286 A K k x s i)). Qed.
Lemma lem4400790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400791 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term287 A K k x s i) = (term288 A K k x s i).
Proof. exact (MK_COMB (@lem4400790) (@lem4400789 A K k x s i)). Qed.
Lemma lem4400792 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term289 A K k x i) = (term206 A K k x i).
Proof. exact (eq_refl (term289 A K k x i)). Qed.
Lemma lem4400793 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term290 A K s k x i) = (term139 A K s k x i).
Proof. exact (MK_COMB (@lem4400791 A K k x s i) (@lem4400792 A K k x i)). Qed.
Lemma lem4400794 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term291 A K s k x) = (term141 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400793 A K s k x i)). Qed.
Lemma lem4400795 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400796 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term283 A K s k x) = (term142 A K s k x).
Proof. exact (MK_COMB (@lem4400795 K) (@lem4400794 A K s k x)). Qed.
Lemma lem4400797 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4400798 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term292 A K s k x) = (term293 A K s k x).
Proof. exact (MK_COMB (@lem4400797) (@lem4400796 A K s k x)). Qed.
Lemma lem4400799 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term286 A K k x s i) = (term177 A K k x s i).
Proof. exact (eq_refl (term286 A K k x s i)). Qed.
Lemma lem4400800 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term294 A K k x s) = (term185 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4400799 A K k x s i)). Qed.
Lemma lem4400801 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400802 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term295 A K k x s) = (term186 A K k x s).
Proof. exact (MK_COMB (@lem4400801 K) (@lem4400800 A K k x s)). Qed.
Lemma lem4400803 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4400804 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term296 A K k x s) = (term297 A K k x s).
Proof. exact (MK_COMB (@lem4400803) (@lem4400802 A K k x s)). Qed.
Lemma lem4400805 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term289 A K k x i) = (term206 A K k x i).
Proof. exact (eq_refl (term289 A K k x i)). Qed.
Lemma lem4400806 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term298 A K k x) = (term285 A K k x).
Proof. exact (fun_ext (fun i : K => @lem4400805 A K k x i)). Qed.
Lemma lem4400807 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4400808 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term299 A K k x) = (term300 A K k x).
Proof. exact (MK_COMB (@lem4400807 K) (@lem4400806 A K k x)). Qed.
Lemma lem4400809 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term284 A K s k x) = (term301 A K s k x).
Proof. exact (MK_COMB (@lem4400804 A K k x s) (@lem4400808 A K k x)). Qed.
Lemma lem4400810 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term283 A K s k x) = (term284 A K s k x)) = ((term142 A K s k x) = (term301 A K s k x)).
Proof. exact (MK_COMB (@lem4400798 A K s k x) (@lem4400809 A K s k x)). Qed.
Lemma lem4400811 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term142 A K s k x) = (term301 A K s k x).
Proof. exact (EQ_MP (@lem4400810 A K s k x) (@lem4400788 A K s k x)). Qed.
Lemma lem4400908 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term215 A K k x s) = (term215 A K k x s).
Proof. exact (eq_refl (term215 A K k x s)). Qed.
Lemma lem4400909 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term217 A K s k x) = (term302 A K s k x).
Proof. exact (MK_COMB (@lem4400908 A K k x s) (@lem4400811 A K s k x)). Qed.
Lemma lem4400910 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term242 A K s k) = (term303 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4400909 A K s k x)). Qed.
Lemma lem4400911 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4400912 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term257 A K s k) = (term304 A K s k).
Proof. exact (MK_COMB (@lem4400911 A K) (@lem4400910 A K s k)). Qed.
Lemma lem4400961 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term258 A K s k) = (term305 A K s k).
Proof. exact (MK_COMB (@lem4400640 A K s k) (@lem4400912 A K s k)). Qed.
Lemma lem4400962 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term234 A K s k) = (term305 A K s k).
Proof. exact (TRANS (@lem4400318 A K s k) (@lem4400961 A K s k)). Qed.
Lemma lem4400964 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4400965 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term236 K P Q) = (term235 K P Q).
Proof. exact (@lem4400964 K P Q). Qed.
Lemma lem4400966 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term260 A K s k x) = (term259 A K s k x).
Proof. exact (@lem4400965 K (term183 A K k x s) (term261 A K k x)). Qed.
Lemma lem4400967 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term262 A K k x s i) = (term176 A K k x s i).
Proof. exact (eq_refl (term262 A K k x s i)). Qed.
Lemma lem4400968 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term269 A K k x s) = (term183 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4400967 A K k x s i)). Qed.
Lemma lem4400969 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400970 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term270 A K k x s) = (term184 A K k x s).
Proof. exact (MK_COMB (@lem4400969 K) (@lem4400968 A K k x s)). Qed.
Lemma lem4400971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400972 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term271 A K k x s) = (term272 A K k x s).
Proof. exact (MK_COMB (@lem4400971) (@lem4400970 A K k x s)). Qed.
Lemma lem4400973 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term264 A K k x i) = (term200 A K k x i).
Proof. exact (eq_refl (term264 A K k x i)). Qed.
Lemma lem4400974 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term273 A K k x) = (term261 A K k x).
Proof. exact (fun_ext (fun i : K => @lem4400973 A K k x i)). Qed.
Lemma lem4400975 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400976 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term274 A K k x) = (term275 A K k x).
Proof. exact (MK_COMB (@lem4400975 K) (@lem4400974 A K k x)). Qed.
Lemma lem4400977 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term260 A K s k x) = (term276 A K s k x).
Proof. exact (MK_COMB (@lem4400972 A K k x s) (@lem4400976 A K k x)). Qed.
Lemma lem4400978 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4400979 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term306 A K s k x) = (term307 A K s k x).
Proof. exact (MK_COMB (@lem4400978) (@lem4400977 A K s k x)). Qed.
Lemma lem4400980 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term262 A K k x s i) = (term176 A K k x s i).
Proof. exact (eq_refl (term262 A K k x s i)). Qed.
Lemma lem4400981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4400982 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term263 A K k x s i) = (term202 A K k x s i).
Proof. exact (MK_COMB (@lem4400981) (@lem4400980 A K k x s i)). Qed.
Lemma lem4400983 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term264 A K k x i) = (term200 A K k x i).
Proof. exact (eq_refl (term264 A K k x i)). Qed.
Lemma lem4400984 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term265 A K s k x i) = (term204 A K s k x i).
Proof. exact (MK_COMB (@lem4400982 A K k x s i) (@lem4400983 A K k x i)). Qed.
Lemma lem4400985 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term266 A K s k x) = (term212 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400984 A K s k x i)). Qed.
Lemma lem4400986 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400987 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term259 A K s k x) = (term213 A K s k x).
Proof. exact (MK_COMB (@lem4400986 K) (@lem4400985 A K s k x)). Qed.
Lemma lem4400988 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term260 A K s k x) = (term259 A K s k x)) = ((term276 A K s k x) = (term213 A K s k x)).
Proof. exact (MK_COMB (@lem4400979 A K s k x) (@lem4400987 A K s k x)). Qed.
Lemma lem4400989 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term276 A K s k x) = (term213 A K s k x).
Proof. exact (EQ_MP (@lem4400988 A K s k x) (@lem4400966 A K s k x)). Qed.
Lemma lem4400990 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term219 A K k x s) = (term219 A K k x s).
Proof. exact (eq_refl (term219 A K k x s)). Qed.
Lemma lem4400991 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term277 A K s k x) = (term221 A K s k x).
Proof. exact (MK_COMB (@lem4400990 A K k x s) (@lem4400989 A K s k x)). Qed.
Lemma lem4400993 {A : Type'} (P : Prop) (Q : A -> Prop) : (term308 A P Q) = (term309 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4400994 {K : Type'} (P : Prop) (Q : K -> Prop) : (term308 K P Q) = (term309 K P Q).
Proof. exact (@lem4400993 K P Q). Qed.
Lemma lem4400995 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term310 A K s k x) = (term311 A K s k x).
Proof. exact (@lem4400994 K (term193 A K k x s) (term212 A K s k x)). Qed.
Lemma lem4400996 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term312 A K s k x i) = (term204 A K s k x i).
Proof. exact (eq_refl (term312 A K s k x i)). Qed.
Lemma lem4400997 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term313 A K s k x) = (term212 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4400996 A K s k x i)). Qed.
Lemma lem4400998 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4400999 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term314 A K s k x) = (term213 A K s k x).
Proof. exact (MK_COMB (@lem4400998 K) (@lem4400997 A K s k x)). Qed.
Lemma lem4401000 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term219 A K k x s) = (term219 A K k x s).
Proof. exact (eq_refl (term219 A K k x s)). Qed.
Lemma lem4401001 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term310 A K s k x) = (term221 A K s k x).
Proof. exact (MK_COMB (@lem4401000 A K k x s) (@lem4400999 A K s k x)). Qed.
Lemma lem4401002 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401003 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term315 A K s k x) = (term316 A K s k x).
Proof. exact (MK_COMB (@lem4401002) (@lem4401001 A K s k x)). Qed.
Lemma lem4401004 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term312 A K s k x i) = (term204 A K s k x i).
Proof. exact (eq_refl (term312 A K s k x i)). Qed.
Lemma lem4401005 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term219 A K k x s) = (term219 A K k x s).
Proof. exact (eq_refl (term219 A K k x s)). Qed.
Lemma lem4401006 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term317 A K s k x i) = (term318 A K s k x i).
Proof. exact (MK_COMB (@lem4401005 A K k x s) (@lem4401004 A K s k x i)). Qed.
Lemma lem4401007 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term319 A K s k x) = (term320 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4401006 A K s k x i)). Qed.
Lemma lem4401008 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401009 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term311 A K s k x) = (term321 A K s k x).
Proof. exact (MK_COMB (@lem4401008 K) (@lem4401007 A K s k x)). Qed.
Lemma lem4401010 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term310 A K s k x) = (term311 A K s k x)) = ((term221 A K s k x) = (term321 A K s k x)).
Proof. exact (MK_COMB (@lem4401003 A K s k x) (@lem4401009 A K s k x)). Qed.
Lemma lem4401011 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term221 A K s k x) = (term321 A K s k x).
Proof. exact (EQ_MP (@lem4401010 A K s k x) (@lem4400995 A K s k x)). Qed.
Lemma lem4401012 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term277 A K s k x) = (term321 A K s k x).
Proof. exact (TRANS (@lem4400991 A K s k x) (@lem4401011 A K s k x)). Qed.
Lemma lem4401013 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term278 A K s k) = (term322 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4401012 A K s k x)). Qed.
Lemma lem4401014 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4401015 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term279 A K s k) = (term323 A K s k).
Proof. exact (MK_COMB (@lem4401014 A K) (@lem4401013 A K s k)). Qed.
Lemma lem4401016 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401017 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term280 A K s k) = (term324 A K s k).
Proof. exact (MK_COMB (@lem4401016) (@lem4401015 A K s k)). Qed.
Lemma lem4401019 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4401020 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term236 K P Q) = (term235 K P Q).
Proof. exact (@lem4401019 K P Q). Qed.
Lemma lem4401021 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term325 A K k x s) = (term326 A K k x s).
Proof. exact (@lem4401020 K (term171 A K k x) (term183 A K k x s)). Qed.
Lemma lem4401022 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term327 A K k x i) = (term158 A K k x i).
Proof. exact (eq_refl (term327 A K k x i)). Qed.
Lemma lem4401023 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term328 A K k x) = (term171 A K k x).
Proof. exact (fun_ext (fun i : K => @lem4401022 A K k x i)). Qed.
Lemma lem4401024 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401025 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term329 A K k x) = (term172 A K k x).
Proof. exact (MK_COMB (@lem4401024 K) (@lem4401023 A K k x)). Qed.
Lemma lem4401026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401027 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term330 A K k x) = (term188 A K k x).
Proof. exact (MK_COMB (@lem4401026) (@lem4401025 A K k x)). Qed.
Lemma lem4401028 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term262 A K k x s i) = (term176 A K k x s i).
Proof. exact (eq_refl (term262 A K k x s i)). Qed.
Lemma lem4401029 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term269 A K k x s) = (term183 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4401028 A K k x s i)). Qed.
Lemma lem4401030 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401031 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term270 A K k x s) = (term184 A K k x s).
Proof. exact (MK_COMB (@lem4401030 K) (@lem4401029 A K k x s)). Qed.
Lemma lem4401032 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term325 A K k x s) = (term190 A K k x s).
Proof. exact (MK_COMB (@lem4401027 A K k x) (@lem4401031 A K k x s)). Qed.
Lemma lem4401033 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401034 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term331 A K k x s) = (term332 A K k x s).
Proof. exact (MK_COMB (@lem4401033) (@lem4401032 A K k x s)). Qed.
Lemma lem4401035 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term327 A K k x i) = (term158 A K k x i).
Proof. exact (eq_refl (term327 A K k x i)). Qed.
Lemma lem4401036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401037 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term333 A K k x i) = (term334 A K k x i).
Proof. exact (MK_COMB (@lem4401036) (@lem4401035 A K k x i)). Qed.
Lemma lem4401038 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term262 A K k x s i) = (term176 A K k x s i).
Proof. exact (eq_refl (term262 A K k x s i)). Qed.
Lemma lem4401039 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term335 A K k x s i) = (term336 A K k x s i).
Proof. exact (MK_COMB (@lem4401037 A K k x i) (@lem4401038 A K k x s i)). Qed.
Lemma lem4401040 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term337 A K k x s) = (term338 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4401039 A K k x s i)). Qed.
Lemma lem4401041 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401042 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term326 A K k x s) = (term339 A K k x s).
Proof. exact (MK_COMB (@lem4401041 K) (@lem4401040 A K k x s)). Qed.
Lemma lem4401043 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term325 A K k x s) = (term326 A K k x s)) = ((term190 A K k x s) = (term339 A K k x s)).
Proof. exact (MK_COMB (@lem4401034 A K k x s) (@lem4401042 A K k x s)). Qed.
Lemma lem4401044 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term190 A K k x s) = (term339 A K k x s).
Proof. exact (EQ_MP (@lem4401043 A K k x s) (@lem4401021 A K k x s)). Qed.
Lemma lem4401047 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term340 A K k x s) = (term340 A K k x s).
Proof. exact (eq_refl (term340 A K k x s)). Qed.
Lemma lem4401048 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term340 A K k x s) = ((term190 A K k x s) = (term339 A K k x s)).
Proof. exact (eq_refl (term340 A K k x s)). Qed.
Lemma lem4401049 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term341 A K k x s) = (term341 A K k x s).
Proof. exact (eq_refl (term341 A K k x s)). Qed.
Lemma lem4401050 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term340 A K k x s) = (term340 A K k x s)) = ((term340 A K k x s) = ((term190 A K k x s) = (term339 A K k x s))).
Proof. exact (MK_COMB (@lem4401049 A K k x s) (@lem4401048 A K k x s)). Qed.
Lemma lem4401051 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term340 A K k x s) = ((term190 A K k x s) = (term339 A K k x s)).
Proof. exact (eq_refl (term340 A K k x s)). Qed.
Lemma lem4401052 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401053 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term341 A K k x s) = (term342 A K k x s).
Proof. exact (MK_COMB (@lem4401052) (@lem4401051 A K k x s)). Qed.
Lemma lem4401054 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term190 A K k x s) = (term339 A K k x s)) = ((term190 A K k x s) = (term339 A K k x s)).
Proof. exact (eq_refl ((term190 A K k x s) = (term339 A K k x s))). Qed.
Lemma lem4401055 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term340 A K k x s) = ((term190 A K k x s) = (term339 A K k x s))) = (((term190 A K k x s) = (term339 A K k x s)) = ((term190 A K k x s) = (term339 A K k x s))).
Proof. exact (MK_COMB (@lem4401053 A K k x s) (@lem4401054 A K k x s)). Qed.
Lemma lem4401056 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term340 A K k x s) = (term340 A K k x s)) = (((term190 A K k x s) = (term339 A K k x s)) = ((term190 A K k x s) = (term339 A K k x s))).
Proof. exact (TRANS (@lem4401050 A K k x s) (@lem4401055 A K k x s)). Qed.
Lemma lem4401057 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : ((term190 A K k x s) = (term339 A K k x s)) = ((term190 A K k x s) = (term339 A K k x s)).
Proof. exact (EQ_MP (@lem4401056 A K k x s) (@lem4401047 A K k x s)). Qed.
Lemma lem4401058 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term190 A K k x s) = (term339 A K k x s).
Proof. exact (EQ_MP (@lem4401057 A K k x s) (@lem4401044 A K k x s)). Qed.
Lemma lem4401059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401060 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term215 A K k x s) = (term343 A K k x s).
Proof. exact (MK_COMB (@lem4401059) (@lem4401058 A K k x s)). Qed.
Lemma lem4401061 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term301 A K s k x) = (term301 A K s k x).
Proof. exact (eq_refl (term301 A K s k x)). Qed.
Lemma lem4401062 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term302 A K s k x) = (term344 A K s k x).
Proof. exact (MK_COMB (@lem4401060 A K k x s) (@lem4401061 A K s k x)). Qed.
Lemma lem4401064 {A : Type'} (P : A -> Prop) (Q : Prop) : (term345 A P Q) = (term346 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4401065 {K : Type'} (P : K -> Prop) (Q : Prop) : (term345 K P Q) = (term346 K P Q).
Proof. exact (@lem4401064 K P Q). Qed.
Lemma lem4401066 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term347 A K s k x) = (term348 A K s k x).
Proof. exact (@lem4401065 K (term338 A K k x s) (term301 A K s k x)). Qed.
Lemma lem4401067 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term349 A K k x s i) = (term336 A K k x s i).
Proof. exact (eq_refl (term349 A K k x s i)). Qed.
Lemma lem4401068 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term350 A K k x s) = (term338 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4401067 A K k x s i)). Qed.
Lemma lem4401069 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401070 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term351 A K k x s) = (term339 A K k x s).
Proof. exact (MK_COMB (@lem4401069 K) (@lem4401068 A K k x s)). Qed.
Lemma lem4401071 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401072 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term352 A K k x s) = (term343 A K k x s).
Proof. exact (MK_COMB (@lem4401071) (@lem4401070 A K k x s)). Qed.
Lemma lem4401073 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term301 A K s k x) = (term301 A K s k x).
Proof. exact (eq_refl (term301 A K s k x)). Qed.
Lemma lem4401074 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term347 A K s k x) = (term344 A K s k x).
Proof. exact (MK_COMB (@lem4401072 A K k x s) (@lem4401073 A K s k x)). Qed.
Lemma lem4401075 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401076 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term353 A K s k x) = (term354 A K s k x).
Proof. exact (MK_COMB (@lem4401075) (@lem4401074 A K s k x)). Qed.
Lemma lem4401077 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term349 A K k x s i) = (term336 A K k x s i).
Proof. exact (eq_refl (term349 A K k x s i)). Qed.
Lemma lem4401078 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401079 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term355 A K k x s i) = (term356 A K k x s i).
Proof. exact (MK_COMB (@lem4401078) (@lem4401077 A K k x s i)). Qed.
Lemma lem4401080 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term301 A K s k x) = (term301 A K s k x).
Proof. exact (eq_refl (term301 A K s k x)). Qed.
Lemma lem4401081 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term357 A K i s k x) = (term358 A K i s k x).
Proof. exact (MK_COMB (@lem4401079 A K k x s i) (@lem4401080 A K s k x)). Qed.
Lemma lem4401082 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term359 A K s k x) = (term360 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4401081 A K i s k x)). Qed.
Lemma lem4401083 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401084 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term348 A K s k x) = (term361 A K s k x).
Proof. exact (MK_COMB (@lem4401083 K) (@lem4401082 A K s k x)). Qed.
Lemma lem4401085 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term347 A K s k x) = (term348 A K s k x)) = ((term344 A K s k x) = (term361 A K s k x)).
Proof. exact (MK_COMB (@lem4401076 A K s k x) (@lem4401084 A K s k x)). Qed.
Lemma lem4401086 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term344 A K s k x) = (term361 A K s k x).
Proof. exact (EQ_MP (@lem4401085 A K s k x) (@lem4401066 A K s k x)). Qed.
Lemma lem4401087 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term302 A K s k x) = (term361 A K s k x).
Proof. exact (TRANS (@lem4401062 A K s k x) (@lem4401086 A K s k x)). Qed.
Lemma lem4401088 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term303 A K s k) = (term362 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4401087 A K s k x)). Qed.
Lemma lem4401089 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4401090 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term304 A K s k) = (term363 A K s k).
Proof. exact (MK_COMB (@lem4401089 A K) (@lem4401088 A K s k)). Qed.
Lemma lem4401091 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term305 A K s k) = (term364 A K s k).
Proof. exact (MK_COMB (@lem4401017 A K s k) (@lem4401090 A K s k)). Qed.
Lemma lem4401093 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4401094 {A K : Type'} (P : type805 A K) (Q : type805 A K) : (term238 A K P Q) = (term237 A K P Q).
Proof. exact (@lem4401093 (K -> A) P Q). Qed.
Lemma lem4401095 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term365 A K s k) = (term366 A K s k).
Proof. exact (@lem4401094 A K (term322 A K s k) (term362 A K s k)). Qed.
Lemma lem4401096 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term367 A K s k x) = (term321 A K s k x).
Proof. exact (eq_refl (term367 A K s k x)). Qed.
Lemma lem4401097 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term368 A K s k) = (term322 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4401096 A K s k x)). Qed.
Lemma lem4401098 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4401099 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term369 A K s k) = (term323 A K s k).
Proof. exact (MK_COMB (@lem4401098 A K) (@lem4401097 A K s k)). Qed.
Lemma lem4401100 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401101 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term370 A K s k) = (term324 A K s k).
Proof. exact (MK_COMB (@lem4401100) (@lem4401099 A K s k)). Qed.
Lemma lem4401102 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term371 A K s k x) = (term361 A K s k x).
Proof. exact (eq_refl (term371 A K s k x)). Qed.
Lemma lem4401103 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term372 A K s k) = (term362 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4401102 A K s k x)). Qed.
Lemma lem4401104 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4401105 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term373 A K s k) = (term363 A K s k).
Proof. exact (MK_COMB (@lem4401104 A K) (@lem4401103 A K s k)). Qed.
Lemma lem4401106 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term365 A K s k) = (term364 A K s k).
Proof. exact (MK_COMB (@lem4401101 A K s k) (@lem4401105 A K s k)). Qed.
Lemma lem4401107 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401108 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term374 A K s k) = (term375 A K s k).
Proof. exact (MK_COMB (@lem4401107) (@lem4401106 A K s k)). Qed.
Lemma lem4401109 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term367 A K s k x) = (term321 A K s k x).
Proof. exact (eq_refl (term367 A K s k x)). Qed.
Lemma lem4401110 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401111 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term376 A K s k x) = (term377 A K s k x).
Proof. exact (MK_COMB (@lem4401110) (@lem4401109 A K s k x)). Qed.
Lemma lem4401112 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term371 A K s k x) = (term361 A K s k x).
Proof. exact (eq_refl (term371 A K s k x)). Qed.
Lemma lem4401113 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term378 A K s k x) = (term379 A K s k x).
Proof. exact (MK_COMB (@lem4401111 A K s k x) (@lem4401112 A K s k x)). Qed.
Lemma lem4401114 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term380 A K s k) = (term381 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4401113 A K s k x)). Qed.
Lemma lem4401115 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4401116 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term366 A K s k) = (term382 A K s k).
Proof. exact (MK_COMB (@lem4401115 A K) (@lem4401114 A K s k)). Qed.
Lemma lem4401117 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : ((term365 A K s k) = (term366 A K s k)) = ((term364 A K s k) = (term382 A K s k)).
Proof. exact (MK_COMB (@lem4401108 A K s k) (@lem4401116 A K s k)). Qed.
Lemma lem4401118 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term364 A K s k) = (term382 A K s k).
Proof. exact (EQ_MP (@lem4401117 A K s k) (@lem4401095 A K s k)). Qed.
Lemma lem4401120 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term236 A P Q) = (term235 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4401121 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term236 K P Q) = (term235 K P Q).
Proof. exact (@lem4401120 K P Q). Qed.
Lemma lem4401122 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term383 A K s k x) = (term384 A K s k x).
Proof. exact (@lem4401121 K (term320 A K s k x) (term360 A K s k x)). Qed.
Lemma lem4401123 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term385 A K s k x i) = (term318 A K s k x i).
Proof. exact (eq_refl (term385 A K s k x i)). Qed.
Lemma lem4401124 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term386 A K s k x) = (term320 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4401123 A K s k x i)). Qed.
Lemma lem4401125 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401126 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term387 A K s k x) = (term321 A K s k x).
Proof. exact (MK_COMB (@lem4401125 K) (@lem4401124 A K s k x)). Qed.
Lemma lem4401127 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401128 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term388 A K s k x) = (term377 A K s k x).
Proof. exact (MK_COMB (@lem4401127) (@lem4401126 A K s k x)). Qed.
Lemma lem4401129 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term389 A K s k x i) = (term358 A K i s k x).
Proof. exact (eq_refl (term389 A K s k x i)). Qed.
Lemma lem4401130 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term390 A K s k x) = (term360 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4401129 A K i s k x)). Qed.
Lemma lem4401131 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401132 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term391 A K s k x) = (term361 A K s k x).
Proof. exact (MK_COMB (@lem4401131 K) (@lem4401130 A K s k x)). Qed.
Lemma lem4401133 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term383 A K s k x) = (term379 A K s k x).
Proof. exact (MK_COMB (@lem4401128 A K s k x) (@lem4401132 A K s k x)). Qed.
Lemma lem4401134 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401135 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term392 A K s k x) = (term393 A K s k x).
Proof. exact (MK_COMB (@lem4401134) (@lem4401133 A K s k x)). Qed.
Lemma lem4401136 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term385 A K s k x i) = (term318 A K s k x i).
Proof. exact (eq_refl (term385 A K s k x i)). Qed.
Lemma lem4401137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4401138 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term394 A K s k x i) = (term395 A K s k x i).
Proof. exact (MK_COMB (@lem4401137) (@lem4401136 A K s k x i)). Qed.
Lemma lem4401139 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term389 A K s k x i) = (term358 A K i s k x).
Proof. exact (eq_refl (term389 A K s k x i)). Qed.
Lemma lem4401140 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term396 A K s k x i) = (term397 A K i s k x).
Proof. exact (MK_COMB (@lem4401138 A K s k x i) (@lem4401139 A K i s k x)). Qed.
Lemma lem4401141 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term398 A K s k x) = (term399 A K s k x).
Proof. exact (fun_ext (fun i : K => @lem4401140 A K i s k x)). Qed.
Lemma lem4401142 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4401143 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term384 A K s k x) = (term400 A K s k x).
Proof. exact (MK_COMB (@lem4401142 K) (@lem4401141 A K s k x)). Qed.
Lemma lem4401144 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : ((term383 A K s k x) = (term384 A K s k x)) = ((term379 A K s k x) = (term400 A K s k x)).
Proof. exact (MK_COMB (@lem4401135 A K s k x) (@lem4401143 A K s k x)). Qed.
Lemma lem4401145 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term379 A K s k x) = (term400 A K s k x).
Proof. exact (EQ_MP (@lem4401144 A K s k x) (@lem4401122 A K s k x)). Qed.
Lemma lem4401146 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term381 A K s k) = (term401 A K s k).
Proof. exact (fun_ext (fun x : K -> A => @lem4401145 A K s k x)). Qed.
Lemma lem4401147 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4401148 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term382 A K s k) = (term402 A K s k).
Proof. exact (MK_COMB (@lem4401147 A K) (@lem4401146 A K s k)). Qed.
Lemma lem4401149 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term364 A K s k) = (term402 A K s k).
Proof. exact (TRANS (@lem4401118 A K s k) (@lem4401148 A K s k)). Qed.
Lemma lem4401150 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term305 A K s k) = (term402 A K s k).
Proof. exact (TRANS (@lem4401091 A K s k) (@lem4401149 A K s k)). Qed.
Lemma lem4401151 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term234 A K s k) = (term402 A K s k).
Proof. exact (TRANS (@lem4400962 A K s k) (@lem4401150 A K s k)). Qed.
Lemma lem4401152 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : (term149 A K s k) = (term402 A K s k).
Proof. exact (TRANS (@lem4400291 A K s k) (@lem4401151 A K s k)). Qed.
Lemma lem4401153 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (h1 : term149 A K s k) : term402 A K s k.
Proof. exact (EQ_MP (@lem4401152 A K s k) (@lem4400157 A K s k h1)). Qed.
Lemma lem4401168 {A : Type'} (x : A) (y : A) : ((term119 A x y) = (x = y)) = (term403 A x y).
Proof. exact (@lem17784 (term119 A x y) (x = y)). Qed.
Lemma lem4401169 {A : Type'} (x : A) : (term120 A x) = (term404 A x).
Proof. exact (fun_ext (fun y : A => @lem4401168 A x y)). Qed.
Lemma lem4401170 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401171 {A : Type'} (x : A) : (term121 A x) = (term405 A x).
Proof. exact (MK_COMB (@lem4401170 A) (@lem4401169 A x)). Qed.
Lemma lem4401172 {A : Type'} : (term122 A) = (term406 A).
Proof. exact (fun_ext (fun x : A => @lem4401171 A x)). Qed.
Lemma lem4401173 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401174 {A : Type'} : (term99 A) = (term407 A).
Proof. exact (MK_COMB (@lem4401173 A) (@lem4401172 A)). Qed.
Lemma lem4401180 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4401181 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (@lem4401180 A P Q). Qed.
Lemma lem4401182 {A : Type'} (x : A) : (term408 A x) = (term409 A x).
Proof. exact (@lem4401181 A (term410 A x) (term411 A x)). Qed.
Lemma lem4401183 {A : Type'} (x : A) (y : A) : (term412 A x y) = (term413 A x y).
Proof. exact (eq_refl (term412 A x y)). Qed.
Lemma lem4401184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401185 {A : Type'} (x : A) (y : A) : (term414 A x y) = (term415 A x y).
Proof. exact (MK_COMB (@lem4401184) (@lem4401183 A x y)). Qed.
Lemma lem4401186 {A : Type'} (x : A) (y : A) : (term416 A x y) = (term417 A x y).
Proof. exact (eq_refl (term416 A x y)). Qed.
Lemma lem4401187 {A : Type'} (x : A) (y : A) : (term418 A x y) = (term403 A x y).
Proof. exact (MK_COMB (@lem4401185 A x y) (@lem4401186 A x y)). Qed.
Lemma lem4401188 {A : Type'} (x : A) : (term419 A x) = (term404 A x).
Proof. exact (fun_ext (fun y : A => @lem4401187 A x y)). Qed.
Lemma lem4401189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401190 {A : Type'} (x : A) : (term408 A x) = (term405 A x).
Proof. exact (MK_COMB (@lem4401189 A) (@lem4401188 A x)). Qed.
Lemma lem4401191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401192 {A : Type'} (x : A) : (term420 A x) = (term421 A x).
Proof. exact (MK_COMB (@lem4401191) (@lem4401190 A x)). Qed.
Lemma lem4401193 {A : Type'} (x : A) (y : A) : (term412 A x y) = (term413 A x y).
Proof. exact (eq_refl (term412 A x y)). Qed.
Lemma lem4401194 {A : Type'} (x : A) : (term422 A x) = (term410 A x).
Proof. exact (fun_ext (fun y : A => @lem4401193 A x y)). Qed.
Lemma lem4401195 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401196 {A : Type'} (x : A) : (term423 A x) = (term424 A x).
Proof. exact (MK_COMB (@lem4401195 A) (@lem4401194 A x)). Qed.
Lemma lem4401197 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401198 {A : Type'} (x : A) : (term425 A x) = (term426 A x).
Proof. exact (MK_COMB (@lem4401197) (@lem4401196 A x)). Qed.
Lemma lem4401199 {A : Type'} (x : A) (y : A) : (term416 A x y) = (term417 A x y).
Proof. exact (eq_refl (term416 A x y)). Qed.
Lemma lem4401200 {A : Type'} (x : A) : (term427 A x) = (term411 A x).
Proof. exact (fun_ext (fun y : A => @lem4401199 A x y)). Qed.
Lemma lem4401201 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401202 {A : Type'} (x : A) : (term428 A x) = (term429 A x).
Proof. exact (MK_COMB (@lem4401201 A) (@lem4401200 A x)). Qed.
Lemma lem4401203 {A : Type'} (x : A) : (term409 A x) = (term430 A x).
Proof. exact (MK_COMB (@lem4401198 A x) (@lem4401202 A x)). Qed.
Lemma lem4401204 {A : Type'} (x : A) : ((term408 A x) = (term409 A x)) = ((term405 A x) = (term430 A x)).
Proof. exact (MK_COMB (@lem4401192 A x) (@lem4401203 A x)). Qed.
Lemma lem4401205 {A : Type'} (x : A) : (term405 A x) = (term430 A x).
Proof. exact (EQ_MP (@lem4401204 A x) (@lem4401182 A x)). Qed.
Lemma lem4401302 {A : Type'} : (term406 A) = (term431 A).
Proof. exact (fun_ext (fun x : A => @lem4401205 A x)). Qed.
Lemma lem4401303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401304 {A : Type'} : (term407 A) = (term432 A).
Proof. exact (MK_COMB (@lem4401303 A) (@lem4401302 A)). Qed.
Lemma lem4401306 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem4401307 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term281 A P Q) = (term282 A P Q).
Proof. exact (@lem4401306 A P Q). Qed.
Lemma lem4401308 {A : Type'} : (term433 A) = (term434 A).
Proof. exact (@lem4401307 A (term435 A) (term436 A)). Qed.
Lemma lem4401309 {A : Type'} (x : A) : (term437 A x) = (term424 A x).
Proof. exact (eq_refl (term437 A x)). Qed.
Lemma lem4401310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401311 {A : Type'} (x : A) : (term438 A x) = (term426 A x).
Proof. exact (MK_COMB (@lem4401310) (@lem4401309 A x)). Qed.
Lemma lem4401312 {A : Type'} (x : A) : (term439 A x) = (term429 A x).
Proof. exact (eq_refl (term439 A x)). Qed.
Lemma lem4401313 {A : Type'} (x : A) : (term440 A x) = (term430 A x).
Proof. exact (MK_COMB (@lem4401311 A x) (@lem4401312 A x)). Qed.
Lemma lem4401314 {A : Type'} : (term441 A) = (term431 A).
Proof. exact (fun_ext (fun x : A => @lem4401313 A x)). Qed.
Lemma lem4401315 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401316 {A : Type'} : (term433 A) = (term432 A).
Proof. exact (MK_COMB (@lem4401315 A) (@lem4401314 A)). Qed.
Lemma lem4401317 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4401318 {A : Type'} : (term442 A) = (term443 A).
Proof. exact (MK_COMB (@lem4401317) (@lem4401316 A)). Qed.
Lemma lem4401319 {A : Type'} (x : A) : (term437 A x) = (term424 A x).
Proof. exact (eq_refl (term437 A x)). Qed.
Lemma lem4401320 {A : Type'} : (term444 A) = (term435 A).
Proof. exact (fun_ext (fun x : A => @lem4401319 A x)). Qed.
Lemma lem4401321 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401322 {A : Type'} : (term445 A) = (term446 A).
Proof. exact (MK_COMB (@lem4401321 A) (@lem4401320 A)). Qed.
Lemma lem4401323 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401324 {A : Type'} : (term447 A) = (term448 A).
Proof. exact (MK_COMB (@lem4401323) (@lem4401322 A)). Qed.
Lemma lem4401325 {A : Type'} (x : A) : (term439 A x) = (term429 A x).
Proof. exact (eq_refl (term439 A x)). Qed.
Lemma lem4401326 {A : Type'} : (term449 A) = (term436 A).
Proof. exact (fun_ext (fun x : A => @lem4401325 A x)). Qed.
Lemma lem4401327 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401328 {A : Type'} : (term450 A) = (term451 A).
Proof. exact (MK_COMB (@lem4401327 A) (@lem4401326 A)). Qed.
Lemma lem4401329 {A : Type'} : (term434 A) = (term452 A).
Proof. exact (MK_COMB (@lem4401324 A) (@lem4401328 A)). Qed.
Lemma lem4401330 {A : Type'} : ((term433 A) = (term434 A)) = ((term432 A) = (term452 A)).
Proof. exact (MK_COMB (@lem4401318 A) (@lem4401329 A)). Qed.
Lemma lem4401331 {A : Type'} : (term432 A) = (term452 A).
Proof. exact (EQ_MP (@lem4401330 A) (@lem4401308 A)). Qed.
Lemma lem4401438 {A : Type'} : (term407 A) = (term452 A).
Proof. exact (TRANS (@lem4401304 A) (@lem4401331 A)). Qed.
Lemma lem4401439 {A : Type'} : (term99 A) = (term452 A).
Proof. exact (TRANS (@lem4401174 A) (@lem4401438 A)). Qed.
Lemma lem4401440 {A : Type'} (h1 : term99 A) : term452 A.
Proof. exact (EQ_MP (@lem4401439 A) (@lem4400158 A h1)). Qed.
Lemma lem4401728 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term400 A K s k x) : term400 A K s k x.
Proof. exact (h1). Qed.
Lemma lem4401729 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term397 A K i s k x) : term397 A K i s k x.
Proof. exact (h1). Qed.
Lemma lem4401748 {A : Type'} (x : A) (y : A) : (term417 A x y) = (term417 A x y).
Proof. exact (eq_refl (term417 A x y)). Qed.
Lemma lem4401749 {A : Type'} (x : A) : (term411 A x) = (term411 A x).
Proof. exact (fun_ext (fun y : A => @lem4401748 A x y)). Qed.
Lemma lem4401750 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401751 {A : Type'} (x : A) : (term429 A x) = (term429 A x).
Proof. exact (MK_COMB (@lem4401750 A) (@lem4401749 A x)). Qed.
Lemma lem4401752 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (fun_ext (fun x : A => @lem4401751 A x)). Qed.
Lemma lem4401753 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401754 {A : Type'} : (term451 A) = (term451 A).
Proof. exact (MK_COMB (@lem4401753 A) (@lem4401752 A)). Qed.
Lemma lem4401773 {A : Type'} (x : A) (y : A) : (term413 A x y) = (term413 A x y).
Proof. exact (eq_refl (term413 A x y)). Qed.
Lemma lem4401774 {A : Type'} (x : A) : (term410 A x) = (term410 A x).
Proof. exact (fun_ext (fun y : A => @lem4401773 A x y)). Qed.
Lemma lem4401775 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401776 {A : Type'} (x : A) : (term424 A x) = (term424 A x).
Proof. exact (MK_COMB (@lem4401775 A) (@lem4401774 A x)). Qed.
Lemma lem4401777 {A : Type'} : (term435 A) = (term435 A).
Proof. exact (fun_ext (fun x : A => @lem4401776 A x)). Qed.
Lemma lem4401778 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4401779 {A : Type'} : (term446 A) = (term446 A).
Proof. exact (MK_COMB (@lem4401778 A) (@lem4401777 A)). Qed.
Lemma lem4401780 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401781 {A : Type'} : (term448 A) = (term448 A).
Proof. exact (MK_COMB (@lem4401780) (@lem4401779 A)). Qed.
Lemma lem4401782 {A : Type'} : (term452 A) = (term452 A).
Proof. exact (MK_COMB (@lem4401781 A) (@lem4401754 A)). Qed.
Lemma lem4401783 {A : Type'} (h1 : term99 A) : term452 A.
Proof. exact (EQ_MP (@lem4401782 A) (@lem4401440 A h1)). Qed.
Lemma lem4401856 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term206 A K k x i) = (term206 A K k x i).
Proof. exact (eq_refl (term206 A K k x i)). Qed.
Lemma lem4401857 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term285 A K k x) = (term285 A K k x).
Proof. exact (fun_ext (fun i : K => @lem4401856 A K k x i)). Qed.
Lemma lem4401858 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4401859 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term300 A K k x) = (term300 A K k x).
Proof. exact (MK_COMB (@lem4401858 K) (@lem4401857 A K k x)). Qed.
Lemma lem4401878 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term177 A K k x s i) = (term177 A K k x s i).
Proof. exact (eq_refl (term177 A K k x s i)). Qed.
Lemma lem4401879 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term185 A K k x s) = (term185 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4401878 A K k x s i)). Qed.
Lemma lem4401880 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4401881 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term186 A K k x s) = (term186 A K k x s).
Proof. exact (MK_COMB (@lem4401880 K) (@lem4401879 A K k x s)). Qed.
Lemma lem4401882 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4401883 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term297 A K k x s) = (term297 A K k x s).
Proof. exact (MK_COMB (@lem4401882) (@lem4401881 A K k x s)). Qed.
Lemma lem4401884 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term301 A K s k x) = (term301 A K s k x).
Proof. exact (MK_COMB (@lem4401883 A K k x s) (@lem4401859 A K k x)). Qed.
Lemma lem4401927 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term356 A K k x s i) = (term356 A K k x s i).
Proof. exact (eq_refl (term356 A K k x s i)). Qed.
Lemma lem4401928 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term358 A K i s k x) = (term358 A K i s k x).
Proof. exact (MK_COMB (@lem4401927 A K k x s i) (@lem4401884 A K s k x)). Qed.
Lemma lem4401973 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term204 A K s k x i) = (term204 A K s k x i).
Proof. exact (eq_refl (term204 A K s k x i)). Qed.
Lemma lem4401992 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term177 A K k x s i) = (term177 A K k x s i).
Proof. exact (eq_refl (term177 A K k x s i)). Qed.
Lemma lem4401993 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term185 A K k x s) = (term185 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4401992 A K k x s i)). Qed.
Lemma lem4401994 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4401995 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term186 A K k x s) = (term186 A K k x s).
Proof. exact (MK_COMB (@lem4401994 K) (@lem4401993 A K k x s)). Qed.
Lemma lem4402010 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term163 A K k x x') = (term163 A K k x x').
Proof. exact (eq_refl (term163 A K k x x')). Qed.
Lemma lem4402011 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term173 A K k x) = (term173 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4402010 A K k x x')). Qed.
Lemma lem4402012 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4402013 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term174 A K k x) = (term174 A K k x).
Proof. exact (MK_COMB (@lem4402012 K) (@lem4402011 A K k x)). Qed.
Lemma lem4402014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4402015 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term192 A K k x) = (term192 A K k x).
Proof. exact (MK_COMB (@lem4402014) (@lem4402013 A K k x)). Qed.
Lemma lem4402016 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term193 A K k x s) = (term193 A K k x s).
Proof. exact (MK_COMB (@lem4402015 A K k x) (@lem4401995 A K k x s)). Qed.
Lemma lem4402017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4402018 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term219 A K k x s) = (term219 A K k x s).
Proof. exact (MK_COMB (@lem4402017) (@lem4402016 A K k x s)). Qed.
Lemma lem4402019 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term318 A K s k x i) = (term318 A K s k x i).
Proof. exact (MK_COMB (@lem4402018 A K k x s) (@lem4401973 A K s k x i)). Qed.
Lemma lem4402020 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4402021 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) : (term395 A K s k x i) = (term395 A K s k x i).
Proof. exact (MK_COMB (@lem4402020) (@lem4402019 A K s k x i)). Qed.
Lemma lem4402022 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) : (term397 A K i s k x) = (term397 A K i s k x).
Proof. exact (MK_COMB (@lem4402021 A K s k x i) (@lem4401928 A K i s k x)). Qed.
Lemma lem4402023 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term397 A K i s k x) : term397 A K i s k x.
Proof. exact (EQ_MP (@lem4402022 A K i s k x) (@lem4401729 A K i s k x h1)). Qed.
Lemma lem4402026 {A : Type'} (h1 : term99 A) : term451 A.
Proof. exact (proj2 (@lem4401783 A h1)). Qed.
Lemma lem4402027 {A : Type'} (h1 : term99 A) : term446 A.
Proof. exact (proj1 (@lem4401783 A h1)). Qed.
Lemma lem4402028 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term318 A K s k x i.
Proof. exact (h1). Qed.
Lemma lem4402029 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term358 A K i s k x.
Proof. exact (h1). Qed.
Lemma lem4402030 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term204 A K s k x i.
Proof. exact (proj2 (@lem4402028 A K s k x i h1)). Qed.
Lemma lem4402031 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term193 A K k x s.
Proof. exact (proj1 (@lem4402028 A K s k x i h1)). Qed.
Lemma lem4402032 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term186 A K k x s.
Proof. exact (proj2 (@lem4402031 A K s k x i h1)). Qed.
Lemma lem4402033 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term174 A K k x.
Proof. exact (proj1 (@lem4402031 A K s k x i h1)). Qed.
Lemma lem4402034 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term176 A K k x s i.
Proof. exact (h1). Qed.
Lemma lem4402035 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) : term200 A K k x i.
Proof. exact (h1). Qed.
Lemma lem4402040 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term301 A K s k x.
Proof. exact (proj2 (@lem4402029 A K i s k x h1)). Qed.
Lemma lem4402041 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term336 A K k x s i.
Proof. exact (proj1 (@lem4402029 A K i s k x h1)). Qed.
Lemma lem4402042 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term300 A K k x.
Proof. exact (proj2 (@lem4402040 A K i s k x h1)). Qed.
Lemma lem4402043 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term186 A K k x s.
Proof. exact (proj1 (@lem4402040 A K i s k x h1)). Qed.
Lemma lem4402044 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term158 A K k x i) : term158 A K k x i.
Proof. exact (h1). Qed.
Lemma lem4402045 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term176 A K k x s i.
Proof. exact (h1). Qed.
Lemma lem4402134 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term177 A K k x s i) = (term177 A K k x s i).
Proof. exact (eq_refl (term177 A K k x s i)). Qed.
Lemma lem4402135 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term185 A K k x s) = (term185 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4402134 A K k x s i)). Qed.
Lemma lem4402136 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4402138 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term186 A K k x s) = (term186 A K k x s).
Proof. exact (MK_COMB (@lem4402136 K) (@lem4402135 A K k x s)). Qed.
Lemma lem4402139 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term186 A K k x s.
Proof. exact (EQ_MP (@lem4402138 A K k x s) (@lem4402032 A K s k x i h1)). Qed.
Lemma lem4402187 {A : Type'} (x : A) (y : A) : (term413 A x y) = (term413 A x y).
Proof. exact (eq_refl (term413 A x y)). Qed.
Lemma lem4402188 {A : Type'} (x : A) : (term410 A x) = (term410 A x).
Proof. exact (fun_ext (fun y : A => @lem4402187 A x y)). Qed.
Lemma lem4402189 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4402190 {A : Type'} (x : A) : (term424 A x) = (term424 A x).
Proof. exact (MK_COMB (@lem4402189 A) (@lem4402188 A x)). Qed.
Lemma lem4402191 {A : Type'} : (term435 A) = (term435 A).
Proof. exact (fun_ext (fun x : A => @lem4402190 A x)). Qed.
Lemma lem4402192 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4402194 {A : Type'} : (term446 A) = (term446 A).
Proof. exact (MK_COMB (@lem4402192 A) (@lem4402191 A)). Qed.
Lemma lem4402195 {A : Type'} (h1 : term99 A) : term446 A.
Proof. exact (EQ_MP (@lem4402194 A) (@lem4402027 A h1)). Qed.
Lemma lem4402219 {A K : Type'} (k : K -> Prop) (x : K -> A) (x' : K) : (term163 A K k x x') = (term163 A K k x x').
Proof. exact (eq_refl (term163 A K k x x')). Qed.
Lemma lem4402220 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term173 A K k x) = (term173 A K k x).
Proof. exact (fun_ext (fun x' : K => @lem4402219 A K k x x')). Qed.
Lemma lem4402221 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4402223 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term174 A K k x) = (term174 A K k x).
Proof. exact (MK_COMB (@lem4402221 K) (@lem4402220 A K k x)). Qed.
Lemma lem4402224 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term174 A K k x.
Proof. exact (EQ_MP (@lem4402223 A K k x) (@lem4402033 A K s k x i h1)). Qed.
Lemma lem4402301 {A : Type'} (x : A) (y : A) : (term417 A x y) = (term417 A x y).
Proof. exact (eq_refl (term417 A x y)). Qed.
Lemma lem4402302 {A : Type'} (x : A) : (term411 A x) = (term411 A x).
Proof. exact (fun_ext (fun y : A => @lem4402301 A x y)). Qed.
Lemma lem4402303 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4402304 {A : Type'} (x : A) : (term429 A x) = (term429 A x).
Proof. exact (MK_COMB (@lem4402303 A) (@lem4402302 A x)). Qed.
Lemma lem4402305 {A : Type'} : (term436 A) = (term436 A).
Proof. exact (fun_ext (fun x : A => @lem4402304 A x)). Qed.
Lemma lem4402306 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4402308 {A : Type'} : (term451 A) = (term451 A).
Proof. exact (MK_COMB (@lem4402306 A) (@lem4402305 A)). Qed.
Lemma lem4402309 {A : Type'} (h1 : term99 A) : term451 A.
Proof. exact (EQ_MP (@lem4402308 A) (@lem4402026 A h1)). Qed.
Lemma lem4402330 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) : (term206 A K k x i) = (term206 A K k x i).
Proof. exact (eq_refl (term206 A K k x i)). Qed.
Lemma lem4402331 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term285 A K k x) = (term285 A K k x).
Proof. exact (fun_ext (fun i : K => @lem4402330 A K k x i)). Qed.
Lemma lem4402332 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4402334 {A K : Type'} (k : K -> Prop) (x : K -> A) : (term300 A K k x) = (term300 A K k x).
Proof. exact (MK_COMB (@lem4402332 K) (@lem4402331 A K k x)). Qed.
Lemma lem4402335 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term300 A K k x.
Proof. exact (EQ_MP (@lem4402334 A K k x) (@lem4402042 A K i s k x h1)). Qed.
Lemma lem4402415 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) : (term177 A K k x s i) = (term177 A K k x s i).
Proof. exact (eq_refl (term177 A K k x s i)). Qed.
Lemma lem4402416 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term185 A K k x s) = (term185 A K k x s).
Proof. exact (fun_ext (fun i : K => @lem4402415 A K k x s i)). Qed.
Lemma lem4402417 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4402419 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) : (term186 A K k x s) = (term186 A K k x s).
Proof. exact (MK_COMB (@lem4402417 K) (@lem4402416 A K k x s)). Qed.
Lemma lem4402420 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term186 A K k x s.
Proof. exact (EQ_MP (@lem4402419 A K k x s) (@lem4402043 A K i s k x h1)). Qed.
Lemma lem4402469 {A K : Type'} (_50316 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term286 A K k x s _50316.
Proof. exact (@lem4402139 A K s k x i h1 _50316). Qed.
Lemma lem4402470 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50316 : K) : (term286 A K k x s _50316) = (term177 A K k x s _50316).
Proof. exact (eq_refl (term286 A K k x s _50316)). Qed.
Lemma lem4402484 {A : Type'} (_50321 : A) (h1 : term99 A) : term437 A _50321.
Proof. exact (@lem4402195 A h1 _50321). Qed.
Lemma lem4402485 {A : Type'} (_50321 : A) : (term437 A _50321) = (term424 A _50321).
Proof. exact (eq_refl (term437 A _50321)). Qed.
Lemma lem4402486 {A : Type'} (_50321 : A) (h1 : term99 A) : term424 A _50321.
Proof. exact (EQ_MP (@lem4402485 A _50321) (@lem4402484 A _50321 h1)). Qed.
Lemma lem4402487 {A : Type'} (_50321 : A) (_50322 : A) (h1 : term99 A) : term412 A _50321 _50322.
Proof. exact (@lem4402486 A _50321 h1 _50322). Qed.
Lemma lem4402488 {A : Type'} (_50321 : A) (_50322 : A) : (term412 A _50321 _50322) = (term413 A _50321 _50322).
Proof. exact (eq_refl (term412 A _50321 _50322)). Qed.
Lemma lem4402496 {A K : Type'} (_50325 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term453 A K k x _50325.
Proof. exact (@lem4402224 A K s k x i h1 _50325). Qed.
Lemma lem4402497 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50325 : K) : (term453 A K k x _50325) = (term163 A K k x _50325).
Proof. exact (eq_refl (term453 A K k x _50325)). Qed.
Lemma lem4402520 {A : Type'} (_50333 : A) (h1 : term99 A) : term439 A _50333.
Proof. exact (@lem4402309 A h1 _50333). Qed.
Lemma lem4402521 {A : Type'} (_50333 : A) : (term439 A _50333) = (term429 A _50333).
Proof. exact (eq_refl (term439 A _50333)). Qed.
Lemma lem4402522 {A : Type'} (_50333 : A) (h1 : term99 A) : term429 A _50333.
Proof. exact (EQ_MP (@lem4402521 A _50333) (@lem4402520 A _50333 h1)). Qed.
Lemma lem4402523 {A : Type'} (_50333 : A) (_50334 : A) (h1 : term99 A) : term416 A _50333 _50334.
Proof. exact (@lem4402522 A _50333 h1 _50334). Qed.
Lemma lem4402524 {A : Type'} (_50333 : A) (_50334 : A) : (term416 A _50333 _50334) = (term417 A _50333 _50334).
Proof. exact (eq_refl (term416 A _50333 _50334)). Qed.
Lemma lem4402529 {A K : Type'} (_50336 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term289 A K k x _50336.
Proof. exact (@lem4402335 A K i s k x h1 _50336). Qed.
Lemma lem4402530 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50336 : K) : (term289 A K k x _50336) = (term206 A K k x _50336).
Proof. exact (eq_refl (term289 A K k x _50336)). Qed.
Lemma lem4402556 {A K : Type'} (_50345 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term286 A K k x s _50345.
Proof. exact (@lem4402420 A K i s k x h1 _50345). Qed.
Lemma lem4402557 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50345 : K) : (term286 A K k x s _50345) = (term177 A K k x s _50345).
Proof. exact (eq_refl (term286 A K k x s _50345)). Qed.
Lemma lem4402597 {A K : Type'} (_50316 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term177 A K k x s _50316.
Proof. exact (EQ_MP (@lem4402470 A K k x s _50316) (@lem4402469 A K _50316 s k x i h1)). Qed.
Lemma lem4402601 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term194 A K x s i.
Proof. exact (proj2 (@lem4402034 A K k x s i h1)). Qed.
Lemma lem4402619 {A : Type'} (_50321 : A) (_50322 : A) (h1 : term99 A) : term413 A _50321 _50322.
Proof. exact (EQ_MP (@lem4402488 A _50321 _50322) (@lem4402487 A _50321 _50322 h1)). Qed.
Lemma lem4402631 {A K : Type'} (_50325 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term163 A K k x _50325.
Proof. exact (EQ_MP (@lem4402497 A K k x _50325) (@lem4402496 A K _50325 s k x i h1)). Qed.
Lemma lem4402641 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) : term454 A K x i.
Proof. exact (proj2 (@lem4402035 A K k x i h1)). Qed.
Lemma lem4402665 {A : Type'} (_50333 : A) (_50334 : A) (h1 : term99 A) : term417 A _50333 _50334.
Proof. exact (EQ_MP (@lem4402524 A _50333 _50334) (@lem4402523 A _50333 _50334 h1)). Qed.
Lemma lem4402677 {A K : Type'} (_50336 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term206 A K k x _50336.
Proof. exact (EQ_MP (@lem4402530 A K k x _50336) (@lem4402529 A K _50336 i s k x h1)). Qed.
Lemma lem4402681 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term158 A K k x i) : term455 A K x i.
Proof. exact (proj2 (@lem4402044 A K k x i h1)). Qed.
Lemma lem4402711 {A K : Type'} (_50345 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term177 A K k x s _50345.
Proof. exact (EQ_MP (@lem4402557 A K k x s _50345) (@lem4402556 A K _50345 i s k x h1)). Qed.
Lemma lem4402721 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term194 A K x s i.
Proof. exact (proj2 (@lem4402045 A K k x s i h1)). Qed.
Lemma lem4402815 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : @IN K i k.
Proof. exact (proj1 (@lem4402034 A K k x s i h1)). Qed.
Lemma lem4402816 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term456 K i k.
Proof. exact (fun h0 : term159 K i k => @lem4402815 A K k x s i h1). Qed.
Lemma lem4402818 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4402819 {K : Type'} (i : K) (k : K -> Prop) : (term456 K i k) = (@IN K i k).
Proof. exact (@lem4402818 (@IN K i k)). Qed.
Lemma lem4402820 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : @IN K i k.
Proof. exact (EQ_MP (@lem4402819 K i k) (@lem4402816 A K k x s i h1)). Qed.
Lemma lem4402826 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4402827 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : (term177 A K k x s _50316) = (term458 A K x s _50316 k).
Proof. exact (@lem4402826 (term134 A K x s _50316) (term159 K _50316 k)). Qed.
Lemma lem4402833 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4402834 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : (term459 A K k x s _50316) = (term460 A K x s _50316 k).
Proof. exact (MK_COMB (@lem4402833) (@lem4402827 A K x s _50316 k)). Qed.
Lemma lem4402840 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : (term458 A K x s _50316 k) = (term458 A K x s _50316 k).
Proof. exact (eq_refl (term458 A K x s _50316 k)). Qed.
Lemma lem4402841 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : ((term177 A K k x s _50316) = (term458 A K x s _50316 k)) = ((term458 A K x s _50316 k) = (term458 A K x s _50316 k)).
Proof. exact (MK_COMB (@lem4402834 A K x s _50316 k) (@lem4402840 A K x s _50316 k)). Qed.
Lemma lem4402843 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4402844 (x : Prop) : (x = x) = True.
Proof. exact (@lem4402843 Prop x). Qed.
Lemma lem4402845 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : ((term458 A K x s _50316 k) = (term458 A K x s _50316 k)) = True.
Proof. exact (@lem4402844 (term458 A K x s _50316 k)). Qed.
Lemma lem4402846 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : ((term177 A K k x s _50316) = (term458 A K x s _50316 k)) = True.
Proof. exact (TRANS (@lem4402841 A K x s _50316 k) (@lem4402845 A K x s _50316 k)). Qed.
Lemma lem4402847 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : True = ((term177 A K k x s _50316) = (term458 A K x s _50316 k)).
Proof. exact (SYM (@lem4402846 A K x s _50316 k)). Qed.
Lemma lem4402848 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) (k : K -> Prop) : (term177 A K k x s _50316) = (term458 A K x s _50316 k).
Proof. exact (EQ_MP (@lem4402847 A K x s _50316 k) (@lem0)). Qed.
Lemma lem4402849 {A K : Type'} (_50316 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term458 A K x s _50316 k.
Proof. exact (EQ_MP (@lem4402848 A K x s _50316 k) (@lem4402597 A K _50316 s k x i h1)). Qed.
Lemma lem4402851 (b : Prop) (a : Prop) : (a \/ b) = (term461 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4402852 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50316 : K) : (term458 A K x s _50316 k) = (term462 A K k x s _50316).
Proof. exact (@lem4402851 (term159 K _50316 k) (term134 A K x s _50316)). Qed.
Lemma lem4402854 (a : Prop) : (term463 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4402855 {K : Type'} (_50316 : K) (k : K -> Prop) : (term156 K _50316 k) = (@IN K _50316 k).
Proof. exact (@lem4402854 (@IN K _50316 k)). Qed.
Lemma lem4402856 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4402857 {K : Type'} (_50316 : K) (k : K -> Prop) : (term464 K _50316 k) = (term465 K _50316 k).
Proof. exact (MK_COMB (@lem4402856) (@lem4402855 K _50316 k)). Qed.
Lemma lem4402858 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50316 : K) : (term134 A K x s _50316) = (term134 A K x s _50316).
Proof. exact (eq_refl (term134 A K x s _50316)). Qed.
Lemma lem4402859 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50316 : K) : (term462 A K k x s _50316) = (term143 A K k x s _50316).
Proof. exact (MK_COMB (@lem4402857 K _50316 k) (@lem4402858 A K x s _50316)). Qed.
Lemma lem4402860 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50316 : K) : (term458 A K x s _50316 k) = (term143 A K k x s _50316).
Proof. exact (TRANS (@lem4402852 A K k x s _50316) (@lem4402859 A K k x s _50316)). Qed.
Lemma lem4402863 {A K : Type'} (_50316 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term143 A K k x s _50316.
Proof. exact (EQ_MP (@lem4402860 A K k x s _50316) (@lem4402849 A K _50316 s k x i h1)). Qed.
Lemma lem4402864 {A K : Type'} (_50316 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term143 A K k x s _50316.
Proof. exact (@lem4402863 A K _50316 s k x i h1). Qed.
Lemma lem4402865 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term143 A K k x s i.
Proof. exact (@lem4402864 A K i s k x i h1). Qed.
Lemma lem4402868 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term318 A K s k x i) (h2 : term176 A K k x s i) : term134 A K x s i.
Proof. exact (@lem4402865 A K s k x i h1 (@lem4402820 A K k x s i h2)). Qed.
Lemma lem4402869 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term318 A K s k x i) (h2 : term176 A K k x s i) : term466 A K x s i.
Proof. exact (fun h0 : term194 A K x s i => @lem4402868 A K k x s i h1 h2). Qed.
Lemma lem4402871 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4402872 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term466 A K x s i) = (term134 A K x s i).
Proof. exact (@lem4402871 (term134 A K x s i)). Qed.
Lemma lem4402873 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term318 A K s k x i) (h2 : term176 A K k x s i) : term134 A K x s i.
Proof. exact (EQ_MP (@lem4402872 A K x s i) (@lem4402869 A K k x s i h1 h2)). Qed.
Lemma lem4402876 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4402878 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term194 A K x s i) = (term467 A K x s i).
Proof. exact (@lem4402876 (term134 A K x s i)). Qed.
Lemma lem4402881 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term467 A K x s i.
Proof. exact (EQ_MP (@lem4402878 A K x s i) (@lem4402601 A K k x s i h1)). Qed.
Lemma lem4402884 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term318 A K s k x i) (h2 : term176 A K k x s i) : False.
Proof. exact (@lem4402881 A K k x s i h2 (@lem4402873 A K k x s i h1 h2)). Qed.
Lemma lem4402885 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term318 A K s k x i) (h2 : term176 A K k x s i) : term468.
Proof. exact (fun h0 : ~ False => @lem4402884 A K k x s i h1 h2). Qed.
Lemma lem4402887 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4402888 : term468 = False.
Proof. exact (@lem4402887 False). Qed.
Lemma lem4402889 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term318 A K s k x i) (h2 : term176 A K k x s i) : False.
Proof. exact (EQ_MP (@lem4402888) (@lem4402885 A K k x s i h1 h2)). Qed.
Lemma lem4402983 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) : term159 K i k.
Proof. exact (proj1 (@lem4402035 A K k x i h1)). Qed.
Lemma lem4402984 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) : term469 K i k.
Proof. exact (fun h0 : @IN K i k => @lem4402983 A K k x i h1). Qed.
Lemma lem4402986 (p : Prop) : (term470 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4402987 {K : Type'} (i : K) (k : K -> Prop) : (term469 K i k) = (term159 K i k).
Proof. exact (@lem4402986 (@IN K i k)). Qed.
Lemma lem4402988 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) : term159 K i k.
Proof. exact (EQ_MP (@lem4402987 K i k) (@lem4402984 A K k x i h1)). Qed.
Lemma lem4402994 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4402995 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : (term163 A K k x _50325) = (term471 A K x _50325 k).
Proof. exact (@lem4402994 ((x _50325) = (@ARB A)) (@IN K _50325 k)). Qed.
Lemma lem4403003 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403004 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : (term472 A K k x _50325) = (term473 A K x _50325 k).
Proof. exact (MK_COMB (@lem4403003) (@lem4402995 A K x _50325 k)). Qed.
Lemma lem4403012 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : (term471 A K x _50325 k) = (term471 A K x _50325 k).
Proof. exact (eq_refl (term471 A K x _50325 k)). Qed.
Lemma lem4403013 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : ((term163 A K k x _50325) = (term471 A K x _50325 k)) = ((term471 A K x _50325 k) = (term471 A K x _50325 k)).
Proof. exact (MK_COMB (@lem4403004 A K x _50325 k) (@lem4403012 A K x _50325 k)). Qed.
Lemma lem4403015 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4403016 (x : Prop) : (x = x) = True.
Proof. exact (@lem4403015 Prop x). Qed.
Lemma lem4403017 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : ((term471 A K x _50325 k) = (term471 A K x _50325 k)) = True.
Proof. exact (@lem4403016 (term471 A K x _50325 k)). Qed.
Lemma lem4403018 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : ((term163 A K k x _50325) = (term471 A K x _50325 k)) = True.
Proof. exact (TRANS (@lem4403013 A K x _50325 k) (@lem4403017 A K x _50325 k)). Qed.
Lemma lem4403019 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : True = ((term163 A K k x _50325) = (term471 A K x _50325 k)).
Proof. exact (SYM (@lem4403018 A K x _50325 k)). Qed.
Lemma lem4403020 {A K : Type'} (x : K -> A) (_50325 : K) (k : K -> Prop) : (term163 A K k x _50325) = (term471 A K x _50325 k).
Proof. exact (EQ_MP (@lem4403019 A K x _50325 k) (@lem0)). Qed.
Lemma lem4403021 {A K : Type'} (_50325 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term471 A K x _50325 k.
Proof. exact (EQ_MP (@lem4403020 A K x _50325 k) (@lem4402631 A K _50325 s k x i h1)). Qed.
Lemma lem4403023 (b : Prop) (a : Prop) : (a \/ b) = (term461 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4403026 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50325 : K) : (term471 A K x _50325 k) = (term145 A K k x _50325).
Proof. exact (@lem4403023 (@IN K _50325 k) ((x _50325) = (@ARB A))). Qed.
Lemma lem4403029 {A K : Type'} (_50325 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term145 A K k x _50325.
Proof. exact (EQ_MP (@lem4403026 A K k x _50325) (@lem4403021 A K _50325 s k x i h1)). Qed.
Lemma lem4403030 {A K : Type'} (_50325 : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term145 A K k x _50325.
Proof. exact (@lem4403029 A K _50325 s k x i h1). Qed.
Lemma lem4403031 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term318 A K s k x i) : term145 A K k x i.
Proof. exact (@lem4403030 A K i s k x i h1). Qed.
Lemma lem4403034 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) (h2 : term318 A K s k x i) : (x i) = (@ARB A).
Proof. exact (@lem4403031 A K s k x i h2 (@lem4402988 A K k x i h1)). Qed.
Lemma lem4403035 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) (h2 : term318 A K s k x i) : term474 A K x i.
Proof. exact (fun h0 : term455 A K x i => @lem4403034 A K s k x i h1 h2). Qed.
Lemma lem4403037 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403038 {A K : Type'} (x : K -> A) (i : K) : (term474 A K x i) = ((x i) = (@ARB A)).
Proof. exact (@lem4403037 ((x i) = (@ARB A))). Qed.
Lemma lem4403039 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) (h2 : term318 A K s k x i) : (x i) = (@ARB A).
Proof. exact (EQ_MP (@lem4403038 A K x i) (@lem4403035 A K s k x i h1 h2)). Qed.
Lemma lem4403041 (b : Prop) (a : Prop) : (a \/ b) = (term461 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4403042 {A : Type'} (_50321 : A) (_50322 : A) : (term413 A _50321 _50322) = (term475 A _50321 _50322).
Proof. exact (@lem4403041 (term476 A _50321 _50322) (term119 A _50321 _50322)). Qed.
Lemma lem4403044 (a : Prop) : (term463 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4403045 {A : Type'} (_50321 : A) (_50322 : A) : (term477 A _50321 _50322) = (_50321 = _50322).
Proof. exact (@lem4403044 (_50321 = _50322)). Qed.
Lemma lem4403046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4403047 {A : Type'} (_50321 : A) (_50322 : A) : (term478 A _50321 _50322) = (term479 A _50321 _50322).
Proof. exact (MK_COMB (@lem4403046) (@lem4403045 A _50321 _50322)). Qed.
Lemma lem4403048 {A : Type'} (_50321 : A) (_50322 : A) : (term119 A _50321 _50322) = (term119 A _50321 _50322).
Proof. exact (eq_refl (term119 A _50321 _50322)). Qed.
Lemma lem4403049 {A : Type'} (_50321 : A) (_50322 : A) : (term475 A _50321 _50322) = (term480 A _50321 _50322).
Proof. exact (MK_COMB (@lem4403047 A _50321 _50322) (@lem4403048 A _50321 _50322)). Qed.
Lemma lem4403050 {A : Type'} (_50321 : A) (_50322 : A) : (term413 A _50321 _50322) = (term480 A _50321 _50322).
Proof. exact (TRANS (@lem4403042 A _50321 _50322) (@lem4403049 A _50321 _50322)). Qed.
Lemma lem4403053 {A : Type'} (_50321 : A) (_50322 : A) (h1 : term99 A) : term480 A _50321 _50322.
Proof. exact (EQ_MP (@lem4403050 A _50321 _50322) (@lem4402619 A _50321 _50322 h1)). Qed.
Lemma lem4403054 {A : Type'} (_50321 : A) (_50322 : A) (h1 : term99 A) : term480 A _50321 _50322.
Proof. exact (@lem4403053 A _50321 _50322 h1). Qed.
Lemma lem4403055 {A K : Type'} (x : K -> A) (i : K) (h1 : term99 A) : term481 A K x i.
Proof. exact (@lem4403054 A (x i) (@ARB A) h1). Qed.
Lemma lem4403058 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term200 A K k x i) (h3 : term318 A K s k x i) : term130 A K x i.
Proof. exact (@lem4403055 A K x i h1 (@lem4403039 A K s k x i h2 h3)). Qed.
Lemma lem4403059 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term200 A K k x i) (h3 : term318 A K s k x i) : term482 A K x i.
Proof. exact (fun h0 : term454 A K x i => @lem4403058 A K s k x i h1 h2 h3). Qed.
Lemma lem4403061 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403062 {A K : Type'} (x : K -> A) (i : K) : (term482 A K x i) = (term130 A K x i).
Proof. exact (@lem4403061 (term130 A K x i)). Qed.
Lemma lem4403063 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term200 A K k x i) (h3 : term318 A K s k x i) : term130 A K x i.
Proof. exact (EQ_MP (@lem4403062 A K x i) (@lem4403059 A K s k x i h1 h2 h3)). Qed.
Lemma lem4403066 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4403068 {A K : Type'} (x : K -> A) (i : K) : (term454 A K x i) = (term483 A K x i).
Proof. exact (@lem4403066 (term130 A K x i)). Qed.
Lemma lem4403071 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term200 A K k x i) : term483 A K x i.
Proof. exact (EQ_MP (@lem4403068 A K x i) (@lem4402641 A K k x i h1)). Qed.
Lemma lem4403074 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term200 A K k x i) (h3 : term318 A K s k x i) : False.
Proof. exact (@lem4403071 A K k x i h2 (@lem4403063 A K s k x i h1 h2 h3)). Qed.
Lemma lem4403075 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term200 A K k x i) (h3 : term318 A K s k x i) : term468.
Proof. exact (fun h0 : ~ False => @lem4403074 A K s k x i h1 h2 h3). Qed.
Lemma lem4403077 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403078 : term468 = False.
Proof. exact (@lem4403077 False). Qed.
Lemma lem4403079 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term200 A K k x i) (h3 : term318 A K s k x i) : False.
Proof. exact (EQ_MP (@lem4403078) (@lem4403075 A K s k x i h1 h2 h3)). Qed.
Lemma lem4403173 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term158 A K k x i) : term159 K i k.
Proof. exact (proj1 (@lem4402044 A K k x i h1)). Qed.
Lemma lem4403174 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term158 A K k x i) : term469 K i k.
Proof. exact (fun h0 : @IN K i k => @lem4403173 A K k x i h1). Qed.
Lemma lem4403176 (p : Prop) : (term470 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4403177 {K : Type'} (i : K) (k : K -> Prop) : (term469 K i k) = (term159 K i k).
Proof. exact (@lem4403176 (@IN K i k)). Qed.
Lemma lem4403178 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term158 A K k x i) : term159 K i k.
Proof. exact (EQ_MP (@lem4403177 K i k) (@lem4403174 A K k x i h1)). Qed.
Lemma lem4403184 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4403185 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : (term206 A K k x _50336) = (term484 A K x _50336 k).
Proof. exact (@lem4403184 (term130 A K x _50336) (@IN K _50336 k)). Qed.
Lemma lem4403191 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403192 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : (term485 A K k x _50336) = (term486 A K x _50336 k).
Proof. exact (MK_COMB (@lem4403191) (@lem4403185 A K x _50336 k)). Qed.
Lemma lem4403198 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : (term484 A K x _50336 k) = (term484 A K x _50336 k).
Proof. exact (eq_refl (term484 A K x _50336 k)). Qed.
Lemma lem4403199 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : ((term206 A K k x _50336) = (term484 A K x _50336 k)) = ((term484 A K x _50336 k) = (term484 A K x _50336 k)).
Proof. exact (MK_COMB (@lem4403192 A K x _50336 k) (@lem4403198 A K x _50336 k)). Qed.
Lemma lem4403201 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4403202 (x : Prop) : (x = x) = True.
Proof. exact (@lem4403201 Prop x). Qed.
Lemma lem4403203 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : ((term484 A K x _50336 k) = (term484 A K x _50336 k)) = True.
Proof. exact (@lem4403202 (term484 A K x _50336 k)). Qed.
Lemma lem4403204 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : ((term206 A K k x _50336) = (term484 A K x _50336 k)) = True.
Proof. exact (TRANS (@lem4403199 A K x _50336 k) (@lem4403203 A K x _50336 k)). Qed.
Lemma lem4403205 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : True = ((term206 A K k x _50336) = (term484 A K x _50336 k)).
Proof. exact (SYM (@lem4403204 A K x _50336 k)). Qed.
Lemma lem4403206 {A K : Type'} (x : K -> A) (_50336 : K) (k : K -> Prop) : (term206 A K k x _50336) = (term484 A K x _50336 k).
Proof. exact (EQ_MP (@lem4403205 A K x _50336 k) (@lem0)). Qed.
Lemma lem4403207 {A K : Type'} (_50336 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term484 A K x _50336 k.
Proof. exact (EQ_MP (@lem4403206 A K x _50336 k) (@lem4402677 A K _50336 i s k x h1)). Qed.
Lemma lem4403209 (b : Prop) (a : Prop) : (a \/ b) = (term461 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4403212 {A K : Type'} (k : K -> Prop) (x : K -> A) (_50336 : K) : (term484 A K x _50336 k) = (term487 A K k x _50336).
Proof. exact (@lem4403209 (@IN K _50336 k) (term130 A K x _50336)). Qed.
Lemma lem4403215 {A K : Type'} (_50336 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term487 A K k x _50336.
Proof. exact (EQ_MP (@lem4403212 A K k x _50336) (@lem4403207 A K _50336 i s k x h1)). Qed.
Lemma lem4403216 {A K : Type'} (_50336 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term487 A K k x _50336.
Proof. exact (@lem4403215 A K _50336 i s k x h1). Qed.
Lemma lem4403217 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term487 A K k x i.
Proof. exact (@lem4403216 A K i i s k x h1). Qed.
Lemma lem4403220 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term158 A K k x i) (h2 : term358 A K i s k x) : term130 A K x i.
Proof. exact (@lem4403217 A K i s k x h2 (@lem4403178 A K k x i h1)). Qed.
Lemma lem4403221 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term158 A K k x i) (h2 : term358 A K i s k x) : term482 A K x i.
Proof. exact (fun h0 : term454 A K x i => @lem4403220 A K i s k x h1 h2). Qed.
Lemma lem4403223 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403224 {A K : Type'} (x : K -> A) (i : K) : (term482 A K x i) = (term130 A K x i).
Proof. exact (@lem4403223 (term130 A K x i)). Qed.
Lemma lem4403225 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term158 A K k x i) (h2 : term358 A K i s k x) : term130 A K x i.
Proof. exact (EQ_MP (@lem4403224 A K x i) (@lem4403221 A K i s k x h1 h2)). Qed.
Lemma lem4403231 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4403232 {A : Type'} (_50333 : A) (_50334 : A) : (term417 A _50333 _50334) = (term488 A _50333 _50334).
Proof. exact (@lem4403231 (_50333 = _50334) (term489 A _50333 _50334)). Qed.
Lemma lem4403240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403241 {A : Type'} (_50333 : A) (_50334 : A) : (term490 A _50333 _50334) = (term491 A _50333 _50334).
Proof. exact (MK_COMB (@lem4403240) (@lem4403232 A _50333 _50334)). Qed.
Lemma lem4403249 {A : Type'} (_50333 : A) (_50334 : A) : (term488 A _50333 _50334) = (term488 A _50333 _50334).
Proof. exact (eq_refl (term488 A _50333 _50334)). Qed.
Lemma lem4403250 {A : Type'} (_50333 : A) (_50334 : A) : ((term417 A _50333 _50334) = (term488 A _50333 _50334)) = ((term488 A _50333 _50334) = (term488 A _50333 _50334)).
Proof. exact (MK_COMB (@lem4403241 A _50333 _50334) (@lem4403249 A _50333 _50334)). Qed.
Lemma lem4403252 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4403253 (x : Prop) : (x = x) = True.
Proof. exact (@lem4403252 Prop x). Qed.
Lemma lem4403254 {A : Type'} (_50333 : A) (_50334 : A) : ((term488 A _50333 _50334) = (term488 A _50333 _50334)) = True.
Proof. exact (@lem4403253 (term488 A _50333 _50334)). Qed.
Lemma lem4403255 {A : Type'} (_50333 : A) (_50334 : A) : ((term417 A _50333 _50334) = (term488 A _50333 _50334)) = True.
Proof. exact (TRANS (@lem4403250 A _50333 _50334) (@lem4403254 A _50333 _50334)). Qed.
Lemma lem4403256 {A : Type'} (_50333 : A) (_50334 : A) : True = ((term417 A _50333 _50334) = (term488 A _50333 _50334)).
Proof. exact (SYM (@lem4403255 A _50333 _50334)). Qed.
Lemma lem4403257 {A : Type'} (_50333 : A) (_50334 : A) : (term417 A _50333 _50334) = (term488 A _50333 _50334).
Proof. exact (EQ_MP (@lem4403256 A _50333 _50334) (@lem0)). Qed.
Lemma lem4403258 {A : Type'} (_50333 : A) (_50334 : A) (h1 : term99 A) : term488 A _50333 _50334.
Proof. exact (EQ_MP (@lem4403257 A _50333 _50334) (@lem4402665 A _50333 _50334 h1)). Qed.
Lemma lem4403260 (b : Prop) (a : Prop) : (a \/ b) = (term461 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4403261 {A : Type'} (_50333 : A) (_50334 : A) : (term488 A _50333 _50334) = (term492 A _50333 _50334).
Proof. exact (@lem4403260 (term489 A _50333 _50334) (_50333 = _50334)). Qed.
Lemma lem4403263 (a : Prop) : (term463 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4403264 {A : Type'} (_50333 : A) (_50334 : A) : (term493 A _50333 _50334) = (term119 A _50333 _50334).
Proof. exact (@lem4403263 (term119 A _50333 _50334)). Qed.
Lemma lem4403265 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4403266 {A : Type'} (_50333 : A) (_50334 : A) : (term494 A _50333 _50334) = (term495 A _50333 _50334).
Proof. exact (MK_COMB (@lem4403265) (@lem4403264 A _50333 _50334)). Qed.
Lemma lem4403267 {A : Type'} (_50333 : A) (_50334 : A) : (_50333 = _50334) = (_50333 = _50334).
Proof. exact (eq_refl (_50333 = _50334)). Qed.
Lemma lem4403268 {A : Type'} (_50333 : A) (_50334 : A) : (term492 A _50333 _50334) = (term496 A _50333 _50334).
Proof. exact (MK_COMB (@lem4403266 A _50333 _50334) (@lem4403267 A _50333 _50334)). Qed.
Lemma lem4403269 {A : Type'} (_50333 : A) (_50334 : A) : (term488 A _50333 _50334) = (term496 A _50333 _50334).
Proof. exact (TRANS (@lem4403261 A _50333 _50334) (@lem4403268 A _50333 _50334)). Qed.
Lemma lem4403272 {A : Type'} (_50333 : A) (_50334 : A) (h1 : term99 A) : term496 A _50333 _50334.
Proof. exact (EQ_MP (@lem4403269 A _50333 _50334) (@lem4403258 A _50333 _50334 h1)). Qed.
Lemma lem4403273 {A : Type'} (_50333 : A) (_50334 : A) (h1 : term99 A) : term496 A _50333 _50334.
Proof. exact (@lem4403272 A _50333 _50334 h1). Qed.
Lemma lem4403274 {A K : Type'} (x : K -> A) (i : K) (h1 : term99 A) : term497 A K x i.
Proof. exact (@lem4403273 A (x i) (@ARB A) h1). Qed.
Lemma lem4403277 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term158 A K k x i) (h3 : term358 A K i s k x) : (x i) = (@ARB A).
Proof. exact (@lem4403274 A K x i h1 (@lem4403225 A K i s k x h2 h3)). Qed.
Lemma lem4403278 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term158 A K k x i) (h3 : term358 A K i s k x) : term474 A K x i.
Proof. exact (fun h0 : term455 A K x i => @lem4403277 A K i s k x h1 h2 h3). Qed.
Lemma lem4403280 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403281 {A K : Type'} (x : K -> A) (i : K) : (term474 A K x i) = ((x i) = (@ARB A)).
Proof. exact (@lem4403280 ((x i) = (@ARB A))). Qed.
Lemma lem4403282 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term158 A K k x i) (h3 : term358 A K i s k x) : (x i) = (@ARB A).
Proof. exact (EQ_MP (@lem4403281 A K x i) (@lem4403278 A K i s k x h1 h2 h3)). Qed.
Lemma lem4403285 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4403287 {A K : Type'} (x : K -> A) (i : K) : (term455 A K x i) = (term498 A K x i).
Proof. exact (@lem4403285 ((x i) = (@ARB A))). Qed.
Lemma lem4403290 {A K : Type'} (k : K -> Prop) (x : K -> A) (i : K) (h1 : term158 A K k x i) : term498 A K x i.
Proof. exact (EQ_MP (@lem4403287 A K x i) (@lem4402681 A K k x i h1)). Qed.
Lemma lem4403293 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term158 A K k x i) (h3 : term358 A K i s k x) : False.
Proof. exact (@lem4403290 A K k x i h2 (@lem4403282 A K i s k x h1 h2 h3)). Qed.
Lemma lem4403294 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term158 A K k x i) (h3 : term358 A K i s k x) : term468.
Proof. exact (fun h0 : ~ False => @lem4403293 A K i s k x h1 h2 h3). Qed.
Lemma lem4403296 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403297 : term468 = False.
Proof. exact (@lem4403296 False). Qed.
Lemma lem4403298 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term158 A K k x i) (h3 : term358 A K i s k x) : False.
Proof. exact (EQ_MP (@lem4403297) (@lem4403294 A K i s k x h1 h2 h3)). Qed.
Lemma lem4403392 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : @IN K i k.
Proof. exact (proj1 (@lem4402045 A K k x s i h1)). Qed.
Lemma lem4403393 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term456 K i k.
Proof. exact (fun h0 : term159 K i k => @lem4403392 A K k x s i h1). Qed.
Lemma lem4403395 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403396 {K : Type'} (i : K) (k : K -> Prop) : (term456 K i k) = (@IN K i k).
Proof. exact (@lem4403395 (@IN K i k)). Qed.
Lemma lem4403397 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : @IN K i k.
Proof. exact (EQ_MP (@lem4403396 K i k) (@lem4403393 A K k x s i h1)). Qed.
Lemma lem4403403 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4403404 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : (term177 A K k x s _50345) = (term458 A K x s _50345 k).
Proof. exact (@lem4403403 (term134 A K x s _50345) (term159 K _50345 k)). Qed.
Lemma lem4403410 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403411 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : (term459 A K k x s _50345) = (term460 A K x s _50345 k).
Proof. exact (MK_COMB (@lem4403410) (@lem4403404 A K x s _50345 k)). Qed.
Lemma lem4403417 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : (term458 A K x s _50345 k) = (term458 A K x s _50345 k).
Proof. exact (eq_refl (term458 A K x s _50345 k)). Qed.
Lemma lem4403418 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : ((term177 A K k x s _50345) = (term458 A K x s _50345 k)) = ((term458 A K x s _50345 k) = (term458 A K x s _50345 k)).
Proof. exact (MK_COMB (@lem4403411 A K x s _50345 k) (@lem4403417 A K x s _50345 k)). Qed.
Lemma lem4403420 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4403421 (x : Prop) : (x = x) = True.
Proof. exact (@lem4403420 Prop x). Qed.
Lemma lem4403422 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : ((term458 A K x s _50345 k) = (term458 A K x s _50345 k)) = True.
Proof. exact (@lem4403421 (term458 A K x s _50345 k)). Qed.
Lemma lem4403423 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : ((term177 A K k x s _50345) = (term458 A K x s _50345 k)) = True.
Proof. exact (TRANS (@lem4403418 A K x s _50345 k) (@lem4403422 A K x s _50345 k)). Qed.
Lemma lem4403424 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : True = ((term177 A K k x s _50345) = (term458 A K x s _50345 k)).
Proof. exact (SYM (@lem4403423 A K x s _50345 k)). Qed.
Lemma lem4403425 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) (k : K -> Prop) : (term177 A K k x s _50345) = (term458 A K x s _50345 k).
Proof. exact (EQ_MP (@lem4403424 A K x s _50345 k) (@lem0)). Qed.
Lemma lem4403426 {A K : Type'} (_50345 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term458 A K x s _50345 k.
Proof. exact (EQ_MP (@lem4403425 A K x s _50345 k) (@lem4402711 A K _50345 i s k x h1)). Qed.
Lemma lem4403428 (b : Prop) (a : Prop) : (a \/ b) = (term461 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4403429 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50345 : K) : (term458 A K x s _50345 k) = (term462 A K k x s _50345).
Proof. exact (@lem4403428 (term159 K _50345 k) (term134 A K x s _50345)). Qed.
Lemma lem4403431 (a : Prop) : (term463 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4403432 {K : Type'} (_50345 : K) (k : K -> Prop) : (term156 K _50345 k) = (@IN K _50345 k).
Proof. exact (@lem4403431 (@IN K _50345 k)). Qed.
Lemma lem4403433 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4403434 {K : Type'} (_50345 : K) (k : K -> Prop) : (term464 K _50345 k) = (term465 K _50345 k).
Proof. exact (MK_COMB (@lem4403433) (@lem4403432 K _50345 k)). Qed.
Lemma lem4403435 {A K : Type'} (x : K -> A) (s : type1470 A K) (_50345 : K) : (term134 A K x s _50345) = (term134 A K x s _50345).
Proof. exact (eq_refl (term134 A K x s _50345)). Qed.
Lemma lem4403436 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50345 : K) : (term462 A K k x s _50345) = (term143 A K k x s _50345).
Proof. exact (MK_COMB (@lem4403434 K _50345 k) (@lem4403435 A K x s _50345)). Qed.
Lemma lem4403437 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (_50345 : K) : (term458 A K x s _50345 k) = (term143 A K k x s _50345).
Proof. exact (TRANS (@lem4403429 A K k x s _50345) (@lem4403436 A K k x s _50345)). Qed.
Lemma lem4403440 {A K : Type'} (_50345 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term143 A K k x s _50345.
Proof. exact (EQ_MP (@lem4403437 A K k x s _50345) (@lem4403426 A K _50345 i s k x h1)). Qed.
Lemma lem4403441 {A K : Type'} (_50345 : K) (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term143 A K k x s _50345.
Proof. exact (@lem4403440 A K _50345 i s k x h1). Qed.
Lemma lem4403442 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term358 A K i s k x) : term143 A K k x s i.
Proof. exact (@lem4403441 A K i i s k x h1). Qed.
Lemma lem4403445 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term176 A K k x s i) (h2 : term358 A K i s k x) : term134 A K x s i.
Proof. exact (@lem4403442 A K i s k x h2 (@lem4403397 A K k x s i h1)). Qed.
Lemma lem4403446 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term176 A K k x s i) (h2 : term358 A K i s k x) : term466 A K x s i.
Proof. exact (fun h0 : term194 A K x s i => @lem4403445 A K i s k x h1 h2). Qed.
Lemma lem4403448 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403449 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term466 A K x s i) = (term134 A K x s i).
Proof. exact (@lem4403448 (term134 A K x s i)). Qed.
Lemma lem4403450 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term176 A K k x s i) (h2 : term358 A K i s k x) : term134 A K x s i.
Proof. exact (EQ_MP (@lem4403449 A K x s i) (@lem4403446 A K i s k x h1 h2)). Qed.
Lemma lem4403453 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4403455 {A K : Type'} (x : K -> A) (s : type1470 A K) (i : K) : (term194 A K x s i) = (term467 A K x s i).
Proof. exact (@lem4403453 (term134 A K x s i)). Qed.
Lemma lem4403458 {A K : Type'} (k : K -> Prop) (x : K -> A) (s : type1470 A K) (i : K) (h1 : term176 A K k x s i) : term467 A K x s i.
Proof. exact (EQ_MP (@lem4403455 A K x s i) (@lem4402721 A K k x s i h1)). Qed.
Lemma lem4403461 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term176 A K k x s i) (h2 : term358 A K i s k x) : False.
Proof. exact (@lem4403458 A K k x s i h1 (@lem4403450 A K i s k x h1 h2)). Qed.
Lemma lem4403462 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term176 A K k x s i) (h2 : term358 A K i s k x) : term468.
Proof. exact (fun h0 : ~ False => @lem4403461 A K i s k x h1 h2). Qed.
Lemma lem4403464 (p : Prop) : (term457 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4403465 : term468 = False.
Proof. exact (@lem4403464 False). Qed.
Lemma lem4403466 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term176 A K k x s i) (h2 : term358 A K i s k x) : False.
Proof. exact (EQ_MP (@lem4403465) (@lem4403462 A K i s k x h1 h2)). Qed.
Lemma lem4403467 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term358 A K i s k x) : False.
Proof. exact (or_elim (@lem4402041 A K i s k x h2) (fun h0 : term158 A K k x i => @lem4403298 A K i s k x h1 h0 h2) (fun h0 : term176 A K k x s i => @lem4403466 A K i s k x h0 h2)). Qed.
Lemma lem4403468 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (i : K) (h1 : term99 A) (h2 : term318 A K s k x i) : False.
Proof. exact (or_elim (@lem4402030 A K s k x i h2) (fun h0 : term176 A K k x s i => @lem4402889 A K k x s i h2 h0) (fun h0 : term200 A K k x i => @lem4403079 A K s k x i h1 h0 h2)). Qed.
Lemma lem4403469 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term397 A K i s k x) : False.
Proof. exact (or_elim (@lem4402023 A K i s k x h2) (fun h0 : term318 A K s k x i => @lem4403468 A K s k x i h1 h0) (fun h0 : term358 A K i s k x => @lem4403467 A K i s k x h1 h0)). Qed.
Lemma lem4403470 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term397 A K i s k x) : (term397 A K i s k x) = False.
Proof. exact (prop_ext (fun h3 : term397 A K i s k x => @lem4403469 A K i s k x h1 h2) (fun h3 : False => @lem4402023 A K i s k x h2)). Qed.
Lemma lem4403471 {A K : Type'} (i : K) (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term397 A K i s k x) : False.
Proof. exact (EQ_MP (@lem4403470 A K i s k x h1 h2) (@lem4402023 A K i s k x h2)). Qed.
Lemma lem4403472 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (x : K -> A) (h1 : term99 A) (h2 : term400 A K s k x) : False.
Proof. exact (ex_elim (@lem4401728 A K s k x h2) (fun i : K => fun h0 : term399 A K s k x i => @lem4403471 A K i s k x h1 h0)). Qed.
Lemma lem4403473 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (h1 : term99 A) (h2 : term149 A K s k) : False.
Proof. exact (ex_elim (@lem4401153 A K s k h2) (fun x : K -> A => fun h0 : term401 A K s k x => @lem4403472 A K s k x h1 h0)). Qed.
Lemma lem4403474 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (h1 : term99 A) (h2 : term149 A K s k) : term104 K.
Proof. exact (fun h0 : term99 K => @lem4403473 A K s k h1 h2). Qed.
Lemma lem4403475 {K : Type'} : (term104 K) = (term105 K).
Proof. exact (@lem69 (term99 K)). Qed.
Lemma lem4403476 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (h1 : term99 A) (h2 : term149 A K s k) : term105 K.
Proof. exact (EQ_MP (@lem4403475 K) (@lem4403474 A K s k h1 h2)). Qed.
Lemma lem4403477 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (h1 : term149 A K s k) : term108 A K.
Proof. exact (fun h0 : term99 A => @lem4403476 A K s k h0 h1). Qed.
Lemma lem4403478 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term151 A K s k.
Proof. exact (fun h0 : term149 A K s k => @lem4403477 A K s k h0). Qed.
Lemma lem4403483 {A K : Type'} (s : type1470 A K) : term153 A K s.
Proof. exact (fun k : K -> Prop => @lem4403478 A K s k). Qed.
Lemma lem4403488 {A K : Type'} : term155 A K.
Proof. exact (fun s : type1470 A K => @lem4403483 A K s). Qed.
Lemma lem4403489 {A K : Type'} : term117 A K.
Proof. exact (EQ_MP (@lem4400156 A K) (@lem4403488 A K)). Qed.
Lemma lem4403490 {A K : Type'} (s : type1470 A K) : term499 A K s.
Proof. exact (@lem4403489 A K s). Qed.
Lemma lem4403491 {A K : Type'} (s : type1470 A K) : (term499 A K s) = (term113 A K s).
Proof. exact (eq_refl (term499 A K s)). Qed.
Lemma lem4403492 {A K : Type'} (s : type1470 A K) : term113 A K s.
Proof. exact (EQ_MP (@lem4403491 A K s) (@lem4403490 A K s)). Qed.
Lemma lem4403493 {A K : Type'} (s : type1470 A K) (k : K -> Prop) : term500 A K s k.
Proof. exact (@lem4403492 A K s k). Qed.
Lemma lem4403494 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term500 A K s k) = (term100 A K k s).
Proof. exact (eq_refl (term500 A K s k)). Qed.
Lemma lem4403495 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term100 A K k s.
Proof. exact (EQ_MP (@lem4403494 A K k s) (@lem4403493 A K s k)). Qed.
Lemma lem4403497 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term100 A K k s.
Proof. exact (@lem4399858 A K k s (@lem4403495 A K k s)). Qed.
Lemma lem4403498 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term98 A K k s) : term107 A K.
Proof. exact (@lem4403497 A K k s (@lem4399837 A K k s h1)). Qed.
Lemma lem4403499 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term98 A K k s) : term104 K.
Proof. exact (@lem4403498 A K k s h1 (@lem4399839 A)). Qed.
Lemma lem4403500 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term98 A K k s) : False.
Proof. exact (@lem4403499 A K k s h1 (@lem4399838 K)). Qed.
Lemma lem4403501 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term98 A K k s) : (term98 A K k s) = False.
Proof. exact (prop_ext (fun h2 : term98 A K k s => @lem4403500 A K k s h1) (fun h2 : False => @lem4399837 A K k s h1)). Qed.
Lemma lem4403502 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (h1 : term98 A K k s) : False.
Proof. exact (EQ_MP (@lem4403501 A K k s h1) (@lem4399837 A K k s h1)). Qed.
Lemma lem4403503 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term97 A K k s.
Proof. exact (fun h0 : term98 A K k s => @lem4403502 A K k s h0). Qed.
Lemma lem4403504 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term95 A K k s.
Proof. exact (EQ_MP (@lem4399836 A K k s) (@lem4403503 A K k s)). Qed.
Lemma lem4403505 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term22 A K k s.
Proof. exact (EQ_MP (@lem4399832 A K k s) (@lem4403504 A K k s)). Qed.
Lemma lem4403506 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term21 A K k s).
Proof. exact (EQ_MP (@lem4399661 A K k s) (@lem4403505 A K k s)). Qed.
Lemma lem4403511 {A K : Type'} (k : K -> Prop) : term501 A K k.
Proof. exact (fun s : type1470 A K => @lem4403506 A K k s). Qed.
Lemma lem4403516 {A K : Type'} : term502 A K.
Proof. exact (fun k : K -> Prop => @lem4403511 A K k). Qed.
