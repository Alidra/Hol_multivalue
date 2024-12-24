Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_IN_CARTESIAN_PRODUCT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import EXTENSIONAL_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import RESTRICTION_spec.
Require Import cartesian_product_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21735_spec.
Require Import thm21736_spec.
Require Import thm21760_spec.
Require Import thm3184714_spec.
Require Import thm3184717_spec.
Require Import thm3184736_spec.
Require Import thm3184739_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Lemma lem4403537 {_83152 : Type'} : term0 _83152.
Proof. exact (EQ_MP (@lem3184717 _83152) (@lem3184714 _83152)). Qed.
Lemma lem4403538 {_83152 : Type'} (p : _83152 -> Prop) : term1 _83152 p.
Proof. exact (@lem4403537 _83152 p). Qed.
Lemma lem4403539 {_83152 : Type'} (p : _83152 -> Prop) : (term1 _83152 p) = (term2 _83152 p).
Proof. exact (eq_refl (term1 _83152 p)). Qed.
Lemma lem4403540 {_83152 : Type'} (p : _83152 -> Prop) : term2 _83152 p.
Proof. exact (EQ_MP (@lem4403539 _83152 p) (@lem4403538 _83152 p)). Qed.
Lemma lem4403541 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : term3 _83152 p x.
Proof. exact (@lem4403540 _83152 p x). Qed.
Lemma lem4403542 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term3 _83152 p x) = ((term4 _83152 p x) = (p x)).
Proof. exact (eq_refl (term3 _83152 p x)). Qed.
Lemma lem4403551 {_83095 : Type'} : term5 _83095.
Proof. exact (EQ_MP (@lem3184739 _83095) (@lem3184736 _83095)). Qed.
Lemma lem4403552 {_83095 : Type'} (p : _83095 -> Prop) : term6 _83095 p.
Proof. exact (@lem4403551 _83095 p). Qed.
Lemma lem4403553 {_83095 : Type'} (p : _83095 -> Prop) : (term6 _83095 p) = (term7 _83095 p).
Proof. exact (eq_refl (term6 _83095 p)). Qed.
Lemma lem4403554 {_83095 : Type'} (p : _83095 -> Prop) : term7 _83095 p.
Proof. exact (EQ_MP (@lem4403553 _83095 p) (@lem4403552 _83095 p)). Qed.
Lemma lem4403555 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : term8 _83095 p x.
Proof. exact (@lem4403554 _83095 p x). Qed.
Lemma lem4403556 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term8 _83095 p x) = ((term9 _83095 x p) = (p x)).
Proof. exact (eq_refl (term8 _83095 p x)). Qed.
Lemma lem4403565 {A B : Type'} (s : A -> Prop) : term10 A B s.
Proof. exact (@lem4382798 A B s). Qed.
Lemma lem4403566 {A B : Type'} (s : A -> Prop) : (term10 A B s) = ((@EXTENSIONAL A B s) = (term11 A B s)).
Proof. exact (eq_refl (term10 A B s)). Qed.
Lemma lem4403568 {A K : Type'} (k : K -> Prop) : term12 A K k.
Proof. exact (@lem4399444 A K k). Qed.
Lemma lem4403569 {A K : Type'} (k : K -> Prop) : (term12 A K k) = (term13 A K k).
Proof. exact (eq_refl (term12 A K k)). Qed.
Lemma lem4403570 {A K : Type'} (k : K -> Prop) : term13 A K k.
Proof. exact (EQ_MP (@lem4403569 A K k) (@lem4403568 A K k)). Qed.
Lemma lem4403571 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term14 A K k s.
Proof. exact (@lem4403570 A K k s). Qed.
Lemma lem4403572 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term14 A K k s) = ((@cartesian_product A K k s) = (term15 A K k s)).
Proof. exact (eq_refl (term14 A K k s)). Qed.
Lemma lem4403574 {A B : Type'} (s : A -> Prop) : term16 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4403575 {A B : Type'} (s : A -> Prop) : (term16 A B s) = (term17 A B s).
Proof. exact (eq_refl (term16 A B s)). Qed.
Lemma lem4403576 {A B : Type'} (s : A -> Prop) : term17 A B s.
Proof. exact (EQ_MP (@lem4403575 A B s) (@lem4403574 A B s)). Qed.
Lemma lem4403577 {A B : Type'} (s : A -> Prop) (f : A -> B) : term18 A B s f.
Proof. exact (@lem4403576 A B s f). Qed.
Lemma lem4403578 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term18 A B s f) = (term19 A B s f).
Proof. exact (eq_refl (term18 A B s f)). Qed.
Lemma lem4403579 {A B : Type'} (s : A -> Prop) (f : A -> B) : term19 A B s f.
Proof. exact (EQ_MP (@lem4403578 A B s f) (@lem4403577 A B s f)). Qed.
Lemma lem4403580 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term20 A B s f x.
Proof. exact (@lem4403579 A B s f x). Qed.
Lemma lem4403581 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term20 A B s f x) = ((@RESTRICTION A B s f x) = (term21 A B s f x)).
Proof. exact (eq_refl (term20 A B s f x)). Qed.
Lemma lem4403598 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (EQ_MP (@lem4403572 A K k s) (@lem4403571 A K k s)). Qed.
Lemma lem4403599 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term15 A K k s).
Proof. exact (@lem4403598 A K k s). Qed.
Lemma lem4403607 {A B : Type'} (s : A -> Prop) : (@EXTENSIONAL A B s) = (term11 A B s).
Proof. exact (EQ_MP (@lem4403566 A B s) (@lem4403565 A B s)). Qed.
Lemma lem4403608 {A K : Type'} (s : K -> Prop) : (@EXTENSIONAL K A s) = (term22 A K s).
Proof. exact (@lem4403607 K A s). Qed.
Lemma lem4403609 {A K : Type'} (k : K -> Prop) : (@EXTENSIONAL K A k) = (term22 A K k).
Proof. exact (@lem4403608 A K k). Qed.
Lemma lem4403622 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4403623 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term23 A K k f).
Proof. exact (MK_COMB (@lem4403609 A K k) (@lem4403622 A K f)). Qed.
Lemma lem4403625 {_83152 : Type'} (p : _83152 -> Prop) (x : _83152) : (term4 _83152 p x) = (p x).
Proof. exact (EQ_MP (@lem4403542 _83152 p x) (@lem4403541 _83152 p x)). Qed.
Lemma lem4403626 {A K : Type'} (p : type805 A K) (x : K -> A) : (term24 A K p x) = (p x).
Proof. exact (@lem4403625 (K -> A) p x). Qed.
Lemma lem4403627 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term25 A K k f) = (term26 A K k f).
Proof. exact (@lem4403626 A K (term27 A K k) f). Qed.
Lemma lem4403628 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term26 A K k f) = (term28 A K k f).
Proof. exact (eq_refl (term26 A K k f)). Qed.
Lemma lem4403629 {A K : Type'} (GEN_PVAR_139 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_139) = (@SETSPEC (K -> A) GEN_PVAR_139).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_139)). Qed.
Lemma lem4403630 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term29 A K GEN_PVAR_139 k f) = (term30 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4403629 A K GEN_PVAR_139) (@lem4403628 A K k f)). Qed.
Lemma lem4403631 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4403632 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) (f : K -> A) : (term31 A K GEN_PVAR_139 k f) = (term32 A K GEN_PVAR_139 k f).
Proof. exact (MK_COMB (@lem4403630 A K GEN_PVAR_139 k f) (@lem4403631 A K f)). Qed.
Lemma lem4403633 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term33 A K GEN_PVAR_139 k) = (term34 A K GEN_PVAR_139 k).
Proof. exact (fun_ext (fun f : K -> A => @lem4403632 A K GEN_PVAR_139 k f)). Qed.
Lemma lem4403634 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4403635 {A K : Type'} (GEN_PVAR_139 : K -> A) (k : K -> Prop) : (term35 A K GEN_PVAR_139 k) = (term36 A K GEN_PVAR_139 k).
Proof. exact (MK_COMB (@lem4403634 A K) (@lem4403633 A K GEN_PVAR_139 k)). Qed.
Lemma lem4403636 {A K : Type'} (k : K -> Prop) : (term37 A K k) = (term38 A K k).
Proof. exact (fun_ext (fun GEN_PVAR_139 : K -> A => @lem4403635 A K GEN_PVAR_139 k)). Qed.
Lemma lem4403637 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4403638 {A K : Type'} (k : K -> Prop) : (term39 A K k) = (term22 A K k).
Proof. exact (MK_COMB (@lem4403637 A K) (@lem4403636 A K k)). Qed.
Lemma lem4403639 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4403640 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term25 A K k f) = (term23 A K k f).
Proof. exact (MK_COMB (@lem4403638 A K k) (@lem4403639 A K f)). Qed.
Lemma lem4403641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403642 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term40 A K k f) = (term41 A K k f).
Proof. exact (MK_COMB (@lem4403641) (@lem4403640 A K k f)). Qed.
Lemma lem4403643 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term26 A K k f) = (term28 A K k f).
Proof. exact (eq_refl (term26 A K k f)). Qed.
Lemma lem4403644 {A K : Type'} (k : K -> Prop) (f : K -> A) : ((term25 A K k f) = (term26 A K k f)) = ((term23 A K k f) = (term28 A K k f)).
Proof. exact (MK_COMB (@lem4403642 A K k f) (@lem4403643 A K k f)). Qed.
Lemma lem4403645 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term23 A K k f) = (term28 A K k f).
Proof. exact (EQ_MP (@lem4403644 A K k f) (@lem4403627 A K k f)). Qed.
Lemma lem4403654 {A K : Type'} (k : K -> Prop) (f : K -> A) : (@EXTENSIONAL K A k f) = (term28 A K k f).
Proof. exact (TRANS (@lem4403623 A K k f) (@lem4403645 A K k f)). Qed.
Lemma lem4403655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4403656 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term42 A K k f) = (term43 A K k f).
Proof. exact (MK_COMB (@lem4403655) (@lem4403654 A K k f)). Qed.
Lemma lem4403663 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term44 A K k f s) = (term44 A K k f s).
Proof. exact (eq_refl (term44 A K k f s)). Qed.
Lemma lem4403664 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term45 A K k f s) = (term46 A K k f s).
Proof. exact (MK_COMB (@lem4403656 A K k f) (@lem4403663 A K k f s)). Qed.
Lemma lem4403667 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4403668 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term47 A K GEN_PVAR_140 k f s) = (term48 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4403667 A K GEN_PVAR_140) (@lem4403664 A K k f s)). Qed.
Lemma lem4403669 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4403670 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term49 A K GEN_PVAR_140 k s f) = (term50 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4403668 A K GEN_PVAR_140 k f s) (@lem4403669 A K f)). Qed.
Lemma lem4403671 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term51 A K GEN_PVAR_140 k s) = (term52 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4403670 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4403672 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4403673 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term53 A K GEN_PVAR_140 k s) = (term54 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4403672 A K) (@lem4403671 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4403678 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term55 A K k s) = (term56 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4403673 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4403679 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4403680 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term15 A K k s) = (term57 A K k s).
Proof. exact (MK_COMB (@lem4403679 A K) (@lem4403678 A K k s)). Qed.
Lemma lem4403681 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (@cartesian_product A K k s) = (term57 A K k s).
Proof. exact (TRANS (@lem4403599 A K k s) (@lem4403680 A K k s)). Qed.
Lemma lem4403682 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term58 A K k f) = (term58 A K k f).
Proof. exact (eq_refl (term58 A K k f)). Qed.
Lemma lem4403683 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term59 A K f k s) = (term60 A K f k s).
Proof. exact (MK_COMB (@lem4403682 A K k f) (@lem4403681 A K k s)). Qed.
Lemma lem4403685 {_83095 : Type'} (p : _83095 -> Prop) (x : _83095) : (term9 _83095 x p) = (p x).
Proof. exact (EQ_MP (@lem4403556 _83095 p x) (@lem4403555 _83095 p x)). Qed.
Lemma lem4403686 {A K : Type'} (p : type805 A K) (x : K -> A) : (term61 A K x p) = (p x).
Proof. exact (@lem4403685 (K -> A) p x). Qed.
Lemma lem4403687 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term62 A K f k s) = (term63 A K s k f).
Proof. exact (@lem4403686 A K (term64 A K k s) (@RESTRICTION K A k f)). Qed.
Lemma lem4403688 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term65 A K k s f) = (term46 A K k f s).
Proof. exact (eq_refl (term65 A K k s f)). Qed.
Lemma lem4403689 {A K : Type'} (GEN_PVAR_140 : K -> A) : (@SETSPEC (K -> A) GEN_PVAR_140) = (@SETSPEC (K -> A) GEN_PVAR_140).
Proof. exact (eq_refl (@SETSPEC (K -> A) GEN_PVAR_140)). Qed.
Lemma lem4403690 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term66 A K GEN_PVAR_140 k s f) = (term48 A K GEN_PVAR_140 k f s).
Proof. exact (MK_COMB (@lem4403689 A K GEN_PVAR_140) (@lem4403688 A K k f s)). Qed.
Lemma lem4403691 {A K : Type'} (f : K -> A) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem4403692 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term67 A K GEN_PVAR_140 k s f) = (term50 A K GEN_PVAR_140 k s f).
Proof. exact (MK_COMB (@lem4403690 A K GEN_PVAR_140 k f s) (@lem4403691 A K f)). Qed.
Lemma lem4403693 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term68 A K GEN_PVAR_140 k s) = (term52 A K GEN_PVAR_140 k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4403692 A K GEN_PVAR_140 k s f)). Qed.
Lemma lem4403694 {A K : Type'} : (@ex (K -> A)) = (@ex (K -> A)).
Proof. exact (eq_refl (@ex (K -> A))). Qed.
Lemma lem4403695 {A K : Type'} (GEN_PVAR_140 : K -> A) (k : K -> Prop) (s : type1470 A K) : (term69 A K GEN_PVAR_140 k s) = (term54 A K GEN_PVAR_140 k s).
Proof. exact (MK_COMB (@lem4403694 A K) (@lem4403693 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4403696 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term70 A K k s) = (term56 A K k s).
Proof. exact (fun_ext (fun GEN_PVAR_140 : K -> A => @lem4403695 A K GEN_PVAR_140 k s)). Qed.
Lemma lem4403697 {A K : Type'} : (@GSPEC (K -> A)) = (@GSPEC (K -> A)).
Proof. exact (eq_refl (@GSPEC (K -> A))). Qed.
Lemma lem4403698 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term71 A K k s) = (term57 A K k s).
Proof. exact (MK_COMB (@lem4403697 A K) (@lem4403696 A K k s)). Qed.
Lemma lem4403699 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term58 A K k f) = (term58 A K k f).
Proof. exact (eq_refl (term58 A K k f)). Qed.
Lemma lem4403700 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term62 A K f k s) = (term60 A K f k s).
Proof. exact (MK_COMB (@lem4403699 A K k f) (@lem4403698 A K k s)). Qed.
Lemma lem4403701 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403702 {A K : Type'} (f : K -> A) (k : K -> Prop) (s : type1470 A K) : (term72 A K f k s) = (term73 A K f k s).
Proof. exact (MK_COMB (@lem4403701) (@lem4403700 A K f k s)). Qed.
Lemma lem4403703 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term63 A K s k f) = (term74 A K k f s).
Proof. exact (eq_refl (term63 A K s k f)). Qed.
Lemma lem4403704 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : ((term62 A K f k s) = (term63 A K s k f)) = ((term60 A K f k s) = (term74 A K k f s)).
Proof. exact (MK_COMB (@lem4403702 A K f k s) (@lem4403703 A K k f s)). Qed.
Lemma lem4403705 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term60 A K f k s) = (term74 A K k f s).
Proof. exact (EQ_MP (@lem4403704 A K k f s) (@lem4403687 A K s k f)). Qed.
Lemma lem4403717 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term21 A B s f x).
Proof. exact (EQ_MP (@lem4403581 A B s f x) (@lem4403580 A B s f x)). Qed.
Lemma lem4403718 {A K : Type'} (s : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A s f x) = (term75 A K s f x).
Proof. exact (@lem4403717 K A s f x). Qed.
Lemma lem4403719 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A k f x) = (term75 A K k f x).
Proof. exact (@lem4403718 A K k f x). Qed.
Lemma lem4403720 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4403721 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term76 A K k f x) = (term77 A K k f x).
Proof. exact (MK_COMB (@lem4403720 A) (@lem4403719 A K k f x)). Qed.
Lemma lem4403722 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4403723 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : ((@RESTRICTION K A k f x) = (@ARB A)) = ((term75 A K k f x) = (@ARB A)).
Proof. exact (MK_COMB (@lem4403721 A K k f x) (@lem4403722 A)). Qed.
Lemma lem4403726 {K : Type'} (x : K) (k : K -> Prop) : (term78 K x k) = (term78 K x k).
Proof. exact (eq_refl (term78 K x k)). Qed.
Lemma lem4403727 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term79 A K k f x) = (term80 A K k f x).
Proof. exact (MK_COMB (@lem4403726 K x k) (@lem4403723 A K k f x)). Qed.
Lemma lem4403730 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term81 A K k f) = (term82 A K k f).
Proof. exact (fun_ext (fun x : K => @lem4403727 A K k f x)). Qed.
Lemma lem4403731 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4403732 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term83 A K k f) = (term84 A K k f).
Proof. exact (MK_COMB (@lem4403731 K) (@lem4403730 A K k f)). Qed.
Lemma lem4403737 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4403738 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term85 A K k f) = (term86 A K k f).
Proof. exact (MK_COMB (@lem4403737) (@lem4403732 A K k f)). Qed.
Lemma lem4403746 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term21 A B s f x).
Proof. exact (EQ_MP (@lem4403581 A B s f x) (@lem4403580 A B s f x)). Qed.
Lemma lem4403747 {A K : Type'} (s : K -> Prop) (f : K -> A) (x : K) : (@RESTRICTION K A s f x) = (term75 A K s f x).
Proof. exact (@lem4403746 K A s f x). Qed.
Lemma lem4403748 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (@RESTRICTION K A k f i) = (term75 A K k f i).
Proof. exact (@lem4403747 A K k f i). Qed.
Lemma lem4403749 {A : Type'} : (@IN A) = (@IN A).
Proof. exact (eq_refl (@IN A)). Qed.
Lemma lem4403750 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term87 A K k f i) = (term88 A K k f i).
Proof. exact (MK_COMB (@lem4403749 A) (@lem4403748 A K k f i)). Qed.
Lemma lem4403751 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4403752 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term89 A K k f s i) = (term90 A K k f s i).
Proof. exact (MK_COMB (@lem4403750 A K k f i) (@lem4403751 A K s i)). Qed.
Lemma lem4403753 {K : Type'} (i : K) (k : K -> Prop) : (term91 K i k) = (term91 K i k).
Proof. exact (eq_refl (term91 K i k)). Qed.
Lemma lem4403754 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) (i : K) : (term92 A K k f s i) = (term93 A K k f s i).
Proof. exact (MK_COMB (@lem4403753 K i k) (@lem4403752 A K k f s i)). Qed.
Lemma lem4403757 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term94 A K k f s) = (term95 A K k f s).
Proof. exact (fun_ext (fun i : K => @lem4403754 A K k f s i)). Qed.
Lemma lem4403758 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4403759 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term96 A K k f s) = (term97 A K k f s).
Proof. exact (MK_COMB (@lem4403758 K) (@lem4403757 A K k f s)). Qed.
Lemma lem4403764 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term74 A K k f s) = (term98 A K k f s).
Proof. exact (MK_COMB (@lem4403738 A K k f) (@lem4403759 A K k f s)). Qed.
Lemma lem4403767 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term60 A K f k s) = (term98 A K k f s).
Proof. exact (TRANS (@lem4403705 A K k f s) (@lem4403764 A K k f s)). Qed.
Lemma lem4403768 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term59 A K f k s) = (term98 A K k f s).
Proof. exact (TRANS (@lem4403683 A K f k s) (@lem4403767 A K k f s)). Qed.
Lemma lem4403769 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403770 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term99 A K f k s) = (term100 A K k f s).
Proof. exact (MK_COMB (@lem4403769) (@lem4403768 A K k f s)). Qed.
Lemma lem4403777 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : (term44 A K k f s) = (term44 A K k f s).
Proof. exact (eq_refl (term44 A K k f s)). Qed.
Lemma lem4403778 {A K : Type'} (k : K -> Prop) (f : K -> A) (s : type1470 A K) : ((term59 A K f k s) = (term44 A K k f s)) = ((term98 A K k f s) = (term44 A K k f s)).
Proof. exact (MK_COMB (@lem4403770 A K k f s) (@lem4403777 A K k f s)). Qed.
Lemma lem4403781 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term101 A K k s) = (term102 A K k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4403778 A K k f s)). Qed.
Lemma lem4403782 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4403783 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term103 A K k s) = (term104 A K k s).
Proof. exact (MK_COMB (@lem4403782 A K) (@lem4403781 A K k s)). Qed.
Lemma lem4403788 {A K : Type'} (k : K -> Prop) : (term105 A K k) = (term106 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4403783 A K k s)). Qed.
Lemma lem4403789 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4403790 {A K : Type'} (k : K -> Prop) : (term107 A K k) = (term108 A K k).
Proof. exact (MK_COMB (@lem4403789 A K) (@lem4403788 A K k)). Qed.
Lemma lem4403795 {A K : Type'} : (term109 A K) = (term110 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4403790 A K k)). Qed.
Lemma lem4403796 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4403797 {A K : Type'} : (term111 A K) = (term112 A K).
Proof. exact (MK_COMB (@lem4403796 K) (@lem4403795 A K)). Qed.
Lemma lem4403802 {A K : Type'} : (term112 A K) = (term111 A K).
Proof. exact (SYM (@lem4403797 A K)). Qed.
Lemma lem4403868 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403869 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4403868 K P x). Qed.
Lemma lem4403870 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem4403869 K k x). Qed.
Lemma lem4403871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4403872 {K : Type'} (k : K -> Prop) (x : K) : (term113 K x k) = (term114 K k x).
Proof. exact (MK_COMB (@lem4403871) (@lem4403870 K k x)). Qed.
Lemma lem4403873 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4403874 {K : Type'} (k : K -> Prop) (x : K) : (term78 K x k) = (term115 K k x).
Proof. exact (MK_COMB (@lem4403873) (@lem4403872 K k x)). Qed.
Lemma lem4403878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403879 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4403878 K P x). Qed.
Lemma lem4403880 {K : Type'} (k : K -> Prop) (x : K) : (@IN K x k) = (k x).
Proof. exact (@lem4403879 K k x). Qed.
Lemma lem4403881 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4403882 {A K : Type'} (k : K -> Prop) (x : K) : (term116 A K x k) = (term117 A K k x).
Proof. exact (MK_COMB (@lem4403881 A) (@lem4403880 K k x)). Qed.
Lemma lem4403883 {A K : Type'} (f : K -> A) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4403884 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term118 A K k f x) = (term119 A K k f x).
Proof. exact (MK_COMB (@lem4403882 A K k x) (@lem4403883 A K f x)). Qed.
Lemma lem4403885 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4403886 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term75 A K k f x) = (term120 A K k f x).
Proof. exact (MK_COMB (@lem4403884 A K k f x) (@lem4403885 A)). Qed.
Lemma lem4403887 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4403888 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term77 A K k f x) = (term121 A K k f x).
Proof. exact (MK_COMB (@lem4403887 A) (@lem4403886 A K k f x)). Qed.
Lemma lem4403889 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4403890 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : ((term75 A K k f x) = (@ARB A)) = ((term120 A K k f x) = (@ARB A)).
Proof. exact (MK_COMB (@lem4403888 A K k f x) (@lem4403889 A)). Qed.
Lemma lem4403893 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term80 A K k f x) = (term122 A K k f x).
Proof. exact (MK_COMB (@lem4403874 K k x) (@lem4403890 A K k f x)). Qed.
Lemma lem4403896 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term82 A K k f) = (term123 A K k f).
Proof. exact (fun_ext (fun x : K => @lem4403893 A K k f x)). Qed.
Lemma lem4403897 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4403898 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term84 A K k f) = (term124 A K k f).
Proof. exact (MK_COMB (@lem4403897 K) (@lem4403896 A K k f)). Qed.
Lemma lem4403903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4403904 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term86 A K k f) = (term125 A K k f).
Proof. exact (MK_COMB (@lem4403903) (@lem4403898 A K k f)). Qed.
Lemma lem4403912 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403913 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4403912 K P x). Qed.
Lemma lem4403914 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4403913 K k i). Qed.
Lemma lem4403915 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4403916 {K : Type'} (k : K -> Prop) (i : K) : (term91 K i k) = (term126 K k i).
Proof. exact (MK_COMB (@lem4403915) (@lem4403914 K k i)). Qed.
Lemma lem4403918 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4403918 A P x). Qed.
Lemma lem4403920 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : (term90 A K k f s i) = (term127 A K s k f i).
Proof. exact (@lem4403919 A (s i) (term75 A K k f i)). Qed.
Lemma lem4403922 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403923 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4403922 K P x). Qed.
Lemma lem4403924 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4403923 K k i). Qed.
Lemma lem4403925 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4403926 {A K : Type'} (k : K -> Prop) (i : K) : (term116 A K i k) = (term117 A K k i).
Proof. exact (MK_COMB (@lem4403925 A) (@lem4403924 K k i)). Qed.
Lemma lem4403927 {A K : Type'} (f : K -> A) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4403928 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term118 A K k f i) = (term119 A K k f i).
Proof. exact (MK_COMB (@lem4403926 A K k i) (@lem4403927 A K f i)). Qed.
Lemma lem4403929 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4403930 {A K : Type'} (k : K -> Prop) (f : K -> A) (i : K) : (term75 A K k f i) = (term120 A K k f i).
Proof. exact (MK_COMB (@lem4403928 A K k f i) (@lem4403929 A)). Qed.
Lemma lem4403931 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4403932 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : (term127 A K s k f i) = (term128 A K s k f i).
Proof. exact (MK_COMB (@lem4403931 A K s i) (@lem4403930 A K k f i)). Qed.
Lemma lem4403933 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : (term90 A K k f s i) = (term128 A K s k f i).
Proof. exact (TRANS (@lem4403920 A K s k f i) (@lem4403932 A K s k f i)). Qed.
Lemma lem4403934 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : (term93 A K k f s i) = (term129 A K s k f i).
Proof. exact (MK_COMB (@lem4403916 K k i) (@lem4403933 A K s k f i)). Qed.
Lemma lem4403937 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term95 A K k f s) = (term130 A K s k f).
Proof. exact (fun_ext (fun i : K => @lem4403934 A K s k f i)). Qed.
Lemma lem4403938 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4403939 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term97 A K k f s) = (term131 A K s k f).
Proof. exact (MK_COMB (@lem4403938 K) (@lem4403937 A K s k f)). Qed.
Lemma lem4403944 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term98 A K k f s) = (term132 A K s k f).
Proof. exact (MK_COMB (@lem4403904 A K k f) (@lem4403939 A K s k f)). Qed.
Lemma lem4403947 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4403948 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) : (term100 A K k f s) = (term133 A K s k f).
Proof. exact (MK_COMB (@lem4403947) (@lem4403944 A K s k f)). Qed.
Lemma lem4403956 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403957 {K : Type'} (P : K -> Prop) (x : K) : (@IN K x P) = (P x).
Proof. exact (@lem4403956 K P x). Qed.
Lemma lem4403958 {K : Type'} (k : K -> Prop) (i : K) : (@IN K i k) = (k i).
Proof. exact (@lem4403957 K k i). Qed.
Lemma lem4403959 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4403960 {K : Type'} (k : K -> Prop) (i : K) : (term91 K i k) = (term126 K k i).
Proof. exact (MK_COMB (@lem4403959) (@lem4403958 K k i)). Qed.
Lemma lem4403962 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4403963 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem4403962 A P x). Qed.
Lemma lem4403964 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term134 A K f s i) = (term135 A K s f i).
Proof. exact (@lem4403963 A (s i) (f i)). Qed.
Lemma lem4403965 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term136 A K k f s i) = (term137 A K k s f i).
Proof. exact (MK_COMB (@lem4403960 K k i) (@lem4403964 A K s f i)). Qed.
Lemma lem4403968 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term138 A K k f s) = (term139 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4403965 A K k s f i)). Qed.
Lemma lem4403969 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4403970 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term44 A K k f s) = (term140 A K k s f).
Proof. exact (MK_COMB (@lem4403969 K) (@lem4403968 A K k s f)). Qed.
Lemma lem4403975 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term98 A K k f s) = (term44 A K k f s)) = ((term132 A K s k f) = (term140 A K k s f)).
Proof. exact (MK_COMB (@lem4403948 A K s k f) (@lem4403970 A K k s f)). Qed.
Lemma lem4403978 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term102 A K k s) = (term141 A K k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4403975 A K k s f)). Qed.
Lemma lem4403979 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4403980 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term104 A K k s) = (term142 A K k s).
Proof. exact (MK_COMB (@lem4403979 A K) (@lem4403978 A K k s)). Qed.
Lemma lem4403985 {A K : Type'} (k : K -> Prop) : (term106 A K k) = (term143 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4403980 A K k s)). Qed.
Lemma lem4403986 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4403987 {A K : Type'} (k : K -> Prop) : (term108 A K k) = (term144 A K k).
Proof. exact (MK_COMB (@lem4403986 A K) (@lem4403985 A K k)). Qed.
Lemma lem4403992 {A K : Type'} : (term110 A K) = (term145 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4403987 A K k)). Qed.
Lemma lem4403993 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4403994 {A K : Type'} : (term112 A K) = (term146 A K).
Proof. exact (MK_COMB (@lem4403993 K) (@lem4403992 A K)). Qed.
Lemma lem4403999 {A K : Type'} : (term146 A K) = (term112 A K).
Proof. exact (SYM (@lem4403994 A K)). Qed.
Lemma lem4404001 (p : Prop) : p = (term147 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4404002 {A K : Type'} : (term146 A K) = (term148 A K).
Proof. exact (@lem4404001 (term146 A K)). Qed.
Lemma lem4404003 {A K : Type'} : (term148 A K) = (term146 A K).
Proof. exact (SYM (@lem4404002 A K)). Qed.
Lemma lem4404004 {A K : Type'} (h1 : term149 A K) : term149 A K.
Proof. exact (h1). Qed.
Lemma lem4404007 {A K : Type'} (h1 : term148 A K) : term148 A K.
Proof. exact (h1). Qed.
Lemma lem4404008 {A K : Type'} : term150 A K.
Proof. exact (fun h0 : term148 A K => @lem4404007 A K h0). Qed.
Lemma lem4404009 {A K : Type'} (h1 : term150 A K) : term150 A K.
Proof. exact (h1). Qed.
Lemma lem4404010 {A K : Type'} (h1 : term148 A K) : term148 A K.
Proof. exact (h1). Qed.
Lemma lem4404011 {A K : Type'} (h1 : term148 A K) (h2 : term150 A K) : term148 A K.
Proof. exact (@lem4404009 A K h2 (@lem4404010 A K h1)). Qed.
Lemma lem4404012 {A K : Type'} (h1 : term148 A K) : term151 A K.
Proof. exact (fun h0 : term150 A K => @lem4404011 A K h1 h0). Qed.
Lemma lem4404013 {A K : Type'} (h1 : term150 A K) : term150 A K.
Proof. exact (h1). Qed.
Lemma lem4404014 {A K : Type'} (h1 : term148 A K) (h2 : term150 A K) : term148 A K.
Proof. exact (@lem4404012 A K h1 (@lem4404013 A K h2)). Qed.
Lemma lem4404015 {A K : Type'} (h1 : term150 A K) : term150 A K.
Proof. exact (fun h0 : term148 A K => @lem4404014 A K h0 h1). Qed.
Lemma lem4404016 {A K : Type'} : term152 A K.
Proof. exact (fun h0 : term150 A K => @lem4404015 A K h0). Qed.
Lemma lem4404019 {A K : Type'} : term150 A K.
Proof. exact (@lem4404016 A K (@lem4404008 A K)). Qed.
Lemma lem4404020 {A K : Type'} : term150 A K.
Proof. exact (@lem4404019 A K). Qed.
Lemma lem4404022 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4404023 {A K : Type'} : (term148 A K) = (term153 A K).
Proof. exact (@lem4404022 (term149 A K)). Qed.
Lemma lem4404025 (t : Prop) : (term154 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4404026 {A K : Type'} : (term153 A K) = (term146 A K).
Proof. exact (@lem4404025 (term146 A K)). Qed.
Lemma lem4404063 {A K : Type'} : (term148 A K) = (term146 A K).
Proof. exact (TRANS (@lem4404023 A K) (@lem4404026 A K)). Qed.
Lemma lem4404068 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term137 A K k s f i) = (term137 A K k s f i).
Proof. exact (eq_refl (term137 A K k s f i)). Qed.
Lemma lem4404069 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term139 A K k s f) = (term139 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404068 A K k s f i)). Qed.
Lemma lem4404070 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404071 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term140 A K k s f) = (term140 A K k s f).
Proof. exact (MK_COMB (@lem4404070 K) (@lem4404069 A K k s f)). Qed.
Lemma lem4404075 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = False) : (k i) = False.
Proof. exact (h1). Qed.
Lemma lem4404076 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4404077 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term126 K k i) = (imp False).
Proof. exact (MK_COMB (@lem4404076) (@lem4404075 K k i h1)). Qed.
Lemma lem4404079 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = False) : (k i) = False.
Proof. exact (h1). Qed.
Lemma lem4404080 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4404081 {A K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term117 A K k i) = (@COND A False).
Proof. exact (MK_COMB (@lem4404080 A) (@lem4404079 K k i h1)). Qed.
Lemma lem4404082 {A K : Type'} (f : K -> A) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4404083 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term119 A K k f i) = (term155 A K f i).
Proof. exact (MK_COMB (@lem4404081 A K k i h1) (@lem4404082 A K f i)). Qed.
Lemma lem4404084 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4404085 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term120 A K k f i) = (term156 A K f i).
Proof. exact (MK_COMB (@lem4404083 A K f k i h1) (@lem4404084 A)). Qed.
Lemma lem4404087 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4404088 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4404087 A t1 t2). Qed.
Lemma lem4404089 {A K : Type'} (f : K -> A) (i : K) : (term156 A K f i) = (@ARB A).
Proof. exact (@lem4404088 A (f i) (@ARB A)). Qed.
Lemma lem4404090 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term120 A K k f i) = (@ARB A).
Proof. exact (TRANS (@lem4404085 A K f k i h1) (@lem4404089 A K f i)). Qed.
Lemma lem4404091 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4404092 {A K : Type'} (f : K -> A) (s : type1470 A K) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term128 A K s k f i) = (s i (@ARB A)).
Proof. exact (MK_COMB (@lem4404091 A K s i) (@lem4404090 A K f k i h1)). Qed.
Lemma lem4404093 {A K : Type'} (f : K -> A) (s : type1470 A K) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term129 A K s k f i) = (term157 A K s i).
Proof. exact (MK_COMB (@lem4404077 K k i h1) (@lem4404092 A K f s k i h1)). Qed.
Lemma lem4404095 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4404096 {A K : Type'} (s : type1470 A K) (i : K) : (term157 A K s i) = True.
Proof. exact (@lem4404095 (s i (@ARB A))). Qed.
Lemma lem4404097 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = False) : (term129 A K s k f i) = True.
Proof. exact (TRANS (@lem4404093 A K f s k i h1) (@lem4404096 A K s i)). Qed.
Lemma lem4404098 {A K : Type'} (s : type1470 A K) (k : K -> Prop) (f : K -> A) (i : K) : term158 A K s k f i.
Proof. exact (fun h0 : (k i) = False => @lem4404097 A K s f k i h0). Qed.
Lemma lem4404100 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = True) : (k i) = True.
Proof. exact (h1). Qed.
Lemma lem4404101 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4404102 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term126 K k i) = (imp True).
Proof. exact (MK_COMB (@lem4404101) (@lem4404100 K k i h1)). Qed.
Lemma lem4404104 {K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = True) : (k i) = True.
Proof. exact (h1). Qed.
Lemma lem4404105 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4404106 {A K : Type'} (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term117 A K k i) = (@COND A True).
Proof. exact (MK_COMB (@lem4404105 A) (@lem4404104 K k i h1)). Qed.
Lemma lem4404107 {A K : Type'} (f : K -> A) (i : K) : (f i) = (f i).
Proof. exact (eq_refl (f i)). Qed.
Lemma lem4404108 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term119 A K k f i) = (term159 A K f i).
Proof. exact (MK_COMB (@lem4404106 A K k i h1) (@lem4404107 A K f i)). Qed.
Lemma lem4404109 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4404110 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term120 A K k f i) = (term160 A K f i).
Proof. exact (MK_COMB (@lem4404108 A K f k i h1) (@lem4404109 A)). Qed.
Lemma lem4404112 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4404113 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4404112 A t2 t1). Qed.
Lemma lem4404114 {A K : Type'} (f : K -> A) (i : K) : (term160 A K f i) = (f i).
Proof. exact (@lem4404113 A (@ARB A) (f i)). Qed.
Lemma lem4404115 {A K : Type'} (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term120 A K k f i) = (f i).
Proof. exact (TRANS (@lem4404110 A K f k i h1) (@lem4404114 A K f i)). Qed.
Lemma lem4404116 {A K : Type'} (s : type1470 A K) (i : K) : (s i) = (s i).
Proof. exact (eq_refl (s i)). Qed.
Lemma lem4404117 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term128 A K s k f i) = (term135 A K s f i).
Proof. exact (MK_COMB (@lem4404116 A K s i) (@lem4404115 A K f k i h1)). Qed.
Lemma lem4404118 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term129 A K s k f i) = (term161 A K s f i).
Proof. exact (MK_COMB (@lem4404102 K k i h1) (@lem4404117 A K s f k i h1)). Qed.
Lemma lem4404120 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4404121 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term161 A K s f i) = (term135 A K s f i).
Proof. exact (@lem4404120 (term135 A K s f i)). Qed.
Lemma lem4404122 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (i : K) (h1 : (k i) = True) : (term129 A K s k f i) = (term135 A K s f i).
Proof. exact (TRANS (@lem4404118 A K s f k i h1) (@lem4404121 A K s f i)). Qed.
Lemma lem4404123 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : term162 A K k s f i.
Proof. exact (fun h0 : (k i) = True => @lem4404122 A K s f k i h0). Qed.
Lemma lem4404124 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : term163 A K k s f i.
Proof. exact (conj (@lem4404098 A K s k f i) (@lem4404123 A K k s f i)). Qed.
Lemma lem4404126 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term164 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4404127 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (i : K) : term165 A K s f k i.
Proof. exact (@lem4404126 (term129 A K s k f i) (term135 A K s f i) (k i) True). Qed.
Lemma lem4404128 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (i : K) : (term129 A K s k f i) = (term166 A K s f k i).
Proof. exact (@lem4404127 A K s f k i (@lem4404124 A K k s f i)). Qed.
Lemma lem4404130 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4404131 {K : Type'} (k : K -> Prop) (i : K) : (term167 K k i) = True.
Proof. exact (@lem4404130 (k i)). Qed.
Lemma lem4404136 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term168 A K k s f i) = (term168 A K k s f i).
Proof. exact (eq_refl (term168 A K k s f i)). Qed.
Lemma lem4404137 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term166 A K s f k i) = (term169 A K k s f i).
Proof. exact (MK_COMB (@lem4404136 A K k s f i) (@lem4404131 K k i)). Qed.
Lemma lem4404139 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem4404140 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term169 A K k s f i) = (term170 A K k s f i).
Proof. exact (@lem4404139 (term170 A K k s f i)). Qed.
Lemma lem4404141 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term166 A K s f k i) = (term170 A K k s f i).
Proof. exact (TRANS (@lem4404137 A K k s f i) (@lem4404140 A K k s f i)). Qed.
Lemma lem4404152 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term129 A K s k f i) = (term170 A K k s f i).
Proof. exact (TRANS (@lem4404128 A K s f k i) (@lem4404141 A K k s f i)). Qed.
Lemma lem4404153 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term130 A K s k f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404152 A K k s f i)). Qed.
Lemma lem4404154 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404155 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term131 A K s k f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404154 K) (@lem4404153 A K k s f)). Qed.
Lemma lem4404159 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (k x) = False.
Proof. exact (h1). Qed.
Lemma lem4404160 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4404161 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term114 K k x) = (~ False).
Proof. exact (MK_COMB (@lem4404160) (@lem4404159 K k x h1)). Qed.
Lemma lem4404163 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4404164 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term114 K k x) = True.
Proof. exact (TRANS (@lem4404161 K k x h1) (@lem4404163)). Qed.
Lemma lem4404165 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4404166 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term115 K k x) = (imp True).
Proof. exact (MK_COMB (@lem4404165) (@lem4404164 K k x h1)). Qed.
Lemma lem4404168 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (k x) = False.
Proof. exact (h1). Qed.
Lemma lem4404169 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4404170 {A K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term117 A K k x) = (@COND A False).
Proof. exact (MK_COMB (@lem4404169 A) (@lem4404168 K k x h1)). Qed.
Lemma lem4404171 {A K : Type'} (f : K -> A) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4404172 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term119 A K k f x) = (term155 A K f x).
Proof. exact (MK_COMB (@lem4404170 A K k x h1) (@lem4404171 A K f x)). Qed.
Lemma lem4404173 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4404174 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term120 A K k f x) = (term156 A K f x).
Proof. exact (MK_COMB (@lem4404172 A K f k x h1) (@lem4404173 A)). Qed.
Lemma lem4404176 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4404177 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem4404176 A t1 t2). Qed.
Lemma lem4404178 {A K : Type'} (f : K -> A) (x : K) : (term156 A K f x) = (@ARB A).
Proof. exact (@lem4404177 A (f x) (@ARB A)). Qed.
Lemma lem4404179 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term120 A K k f x) = (@ARB A).
Proof. exact (TRANS (@lem4404174 A K f k x h1) (@lem4404178 A K f x)). Qed.
Lemma lem4404180 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4404181 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term121 A K k f x) = (@eq A (@ARB A)).
Proof. exact (MK_COMB (@lem4404180 A) (@lem4404179 A K f k x h1)). Qed.
Lemma lem4404182 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4404183 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : ((term120 A K k f x) = (@ARB A)) = ((@ARB A) = (@ARB A)).
Proof. exact (MK_COMB (@lem4404181 A K f k x h1) (@lem4404182 A)). Qed.
Lemma lem4404185 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4404186 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4404185 A x). Qed.
Lemma lem4404187 {A : Type'} : ((@ARB A) = (@ARB A)) = True.
Proof. exact (@lem4404186 A (@ARB A)). Qed.
Lemma lem4404188 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : ((term120 A K k f x) = (@ARB A)) = True.
Proof. exact (TRANS (@lem4404183 A K f k x h1) (@lem4404187 A)). Qed.
Lemma lem4404189 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term122 A K k f x) = (True -> True).
Proof. exact (MK_COMB (@lem4404166 K k x h1) (@lem4404188 A K f k x h1)). Qed.
Lemma lem4404191 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4404192 : (True -> True) = True.
Proof. exact (@lem4404191 True). Qed.
Lemma lem4404193 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = False) : (term122 A K k f x) = True.
Proof. exact (TRANS (@lem4404189 A K f k x h1) (@lem4404192)). Qed.
Lemma lem4404194 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : term173 A K k f x.
Proof. exact (fun h0 : (k x) = False => @lem4404193 A K f k x h0). Qed.
Lemma lem4404196 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (k x) = True.
Proof. exact (h1). Qed.
Lemma lem4404197 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4404198 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term114 K k x) = (~ True).
Proof. exact (MK_COMB (@lem4404197) (@lem4404196 K k x h1)). Qed.
Lemma lem4404200 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem4404201 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term114 K k x) = False.
Proof. exact (TRANS (@lem4404198 K k x h1) (@lem4404200)). Qed.
Lemma lem4404202 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4404203 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term115 K k x) = (imp False).
Proof. exact (MK_COMB (@lem4404202) (@lem4404201 K k x h1)). Qed.
Lemma lem4404205 {K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (k x) = True.
Proof. exact (h1). Qed.
Lemma lem4404206 {A : Type'} : (@COND A) = (@COND A).
Proof. exact (eq_refl (@COND A)). Qed.
Lemma lem4404207 {A K : Type'} (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term117 A K k x) = (@COND A True).
Proof. exact (MK_COMB (@lem4404206 A) (@lem4404205 K k x h1)). Qed.
Lemma lem4404208 {A K : Type'} (f : K -> A) (x : K) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4404209 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term119 A K k f x) = (term159 A K f x).
Proof. exact (MK_COMB (@lem4404207 A K k x h1) (@lem4404208 A K f x)). Qed.
Lemma lem4404210 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4404211 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term120 A K k f x) = (term160 A K f x).
Proof. exact (MK_COMB (@lem4404209 A K f k x h1) (@lem4404210 A)). Qed.
Lemma lem4404213 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4404214 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem4404213 A t2 t1). Qed.
Lemma lem4404215 {A K : Type'} (f : K -> A) (x : K) : (term160 A K f x) = (f x).
Proof. exact (@lem4404214 A (@ARB A) (f x)). Qed.
Lemma lem4404216 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term120 A K k f x) = (f x).
Proof. exact (TRANS (@lem4404211 A K f k x h1) (@lem4404215 A K f x)). Qed.
Lemma lem4404217 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4404218 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term121 A K k f x) = (term174 A K f x).
Proof. exact (MK_COMB (@lem4404217 A) (@lem4404216 A K f k x h1)). Qed.
Lemma lem4404219 {A : Type'} : (@ARB A) = (@ARB A).
Proof. exact (eq_refl (@ARB A)). Qed.
Lemma lem4404220 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : ((term120 A K k f x) = (@ARB A)) = ((f x) = (@ARB A)).
Proof. exact (MK_COMB (@lem4404218 A K f k x h1) (@lem4404219 A)). Qed.
Lemma lem4404223 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term122 A K k f x) = (term175 A K f x).
Proof. exact (MK_COMB (@lem4404203 K k x h1) (@lem4404220 A K f k x h1)). Qed.
Lemma lem4404225 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem4404226 {A K : Type'} (f : K -> A) (x : K) : (term175 A K f x) = True.
Proof. exact (@lem4404225 ((f x) = (@ARB A))). Qed.
Lemma lem4404227 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) (h1 : (k x) = True) : (term122 A K k f x) = True.
Proof. exact (TRANS (@lem4404223 A K f k x h1) (@lem4404226 A K f x)). Qed.
Lemma lem4404228 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : term176 A K k f x.
Proof. exact (fun h0 : (k x) = True => @lem4404227 A K f k x h0). Qed.
Lemma lem4404229 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : term177 A K k f x.
Proof. exact (conj (@lem4404194 A K k f x) (@lem4404228 A K k f x)). Qed.
Lemma lem4404231 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term164 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4404232 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) : term178 A K f k x.
Proof. exact (@lem4404231 (term122 A K k f x) True (k x) True). Qed.
Lemma lem4404233 {A K : Type'} (f : K -> A) (k : K -> Prop) (x : K) : (term122 A K k f x) = (term179 K k x).
Proof. exact (@lem4404232 A K f k x (@lem4404229 A K k f x)). Qed.
Lemma lem4404235 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4404236 {K : Type'} (k : K -> Prop) (x : K) : (term167 K k x) = True.
Proof. exact (@lem4404235 (k x)). Qed.
Lemma lem4404238 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4404239 {K : Type'} (k : K -> Prop) (x : K) : (term180 K k x) = True.
Proof. exact (@lem4404238 (term114 K k x)). Qed.
Lemma lem4404240 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404241 {K : Type'} (k : K -> Prop) (x : K) : (term181 K k x) = (and True).
Proof. exact (MK_COMB (@lem4404240) (@lem4404239 K k x)). Qed.
Lemma lem4404242 {K : Type'} (k : K -> Prop) (x : K) : (term179 K k x) = (True /\ True).
Proof. exact (MK_COMB (@lem4404241 K k x) (@lem4404236 K k x)). Qed.
Lemma lem4404244 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4404245 : (True /\ True) = True.
Proof. exact (@lem4404244 True). Qed.
Lemma lem4404246 {K : Type'} (k : K -> Prop) (x : K) : (term179 K k x) = True.
Proof. exact (TRANS (@lem4404242 K k x) (@lem4404245)). Qed.
Lemma lem4404251 {A K : Type'} (k : K -> Prop) (f : K -> A) (x : K) : (term122 A K k f x) = True.
Proof. exact (TRANS (@lem4404233 A K f k x) (@lem4404246 K k x)). Qed.
Lemma lem4404252 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term123 A K k f) = (term182 K).
Proof. exact (fun_ext (fun x : K => @lem4404251 A K k f x)). Qed.
Lemma lem4404253 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404254 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term124 A K k f) = (term183 K).
Proof. exact (MK_COMB (@lem4404253 K) (@lem4404252 A K k f)). Qed.
Lemma lem4404255 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404256 {A K : Type'} (k : K -> Prop) (f : K -> A) : (term125 A K k f) = (term184 K).
Proof. exact (MK_COMB (@lem4404255) (@lem4404254 A K k f)). Qed.
Lemma lem4404257 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term132 A K s k f) = (term185 A K k s f).
Proof. exact (MK_COMB (@lem4404256 A K k f) (@lem4404155 A K k s f)). Qed.
Lemma lem4404258 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404259 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term133 A K s k f) = (term186 A K k s f).
Proof. exact (MK_COMB (@lem4404258) (@lem4404257 A K k s f)). Qed.
Lemma lem4404260 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term132 A K s k f) = (term140 A K k s f)) = ((term185 A K k s f) = (term140 A K k s f)).
Proof. exact (MK_COMB (@lem4404259 A K k s f) (@lem4404071 A K k s f)). Qed.
Lemma lem4404261 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term141 A K k s) = (term187 A K k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4404260 A K k s f)). Qed.
Lemma lem4404262 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4404263 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term142 A K k s) = (term188 A K k s).
Proof. exact (MK_COMB (@lem4404262 A K) (@lem4404261 A K k s)). Qed.
Lemma lem4404264 {A K : Type'} (k : K -> Prop) : (term143 A K k) = (term189 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4404263 A K k s)). Qed.
Lemma lem4404265 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4404266 {A K : Type'} (k : K -> Prop) : (term144 A K k) = (term190 A K k).
Proof. exact (MK_COMB (@lem4404265 A K) (@lem4404264 A K k)). Qed.
Lemma lem4404267 {A K : Type'} : (term145 A K) = (term191 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4404266 A K k)). Qed.
Lemma lem4404268 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4404269 {A K : Type'} : (term146 A K) = (term192 A K).
Proof. exact (MK_COMB (@lem4404268 K) (@lem4404267 A K)). Qed.
Lemma lem4404270 {A K : Type'} : (term148 A K) = (term192 A K).
Proof. exact (TRANS (@lem4404063 A K) (@lem4404269 A K)). Qed.
Lemma lem4404292 {A : Type'} (t : Prop) : (term193 A t) = t.
Proof. exact (EQ_MP (@lem21736 A t) (@lem21735 A t)). Qed.
Lemma lem4404293 {K : Type'} (t : Prop) : (term193 K t) = t.
Proof. exact (@lem4404292 K t). Qed.
Lemma lem4404294 {K : Type'} : (term183 K) = True.
Proof. exact (@lem4404293 K True). Qed.
Lemma lem4404295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404296 {K : Type'} : (term184 K) = (and True).
Proof. exact (MK_COMB (@lem4404295) (@lem4404294 K)). Qed.
Lemma lem4404305 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (eq_refl (term172 A K k s f)). Qed.
Lemma lem4404306 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term185 A K k s f) = (term194 A K k s f).
Proof. exact (MK_COMB (@lem4404296 K) (@lem4404305 A K k s f)). Qed.
Lemma lem4404308 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem21760 t)). Qed.
Lemma lem4404309 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term194 A K k s f) = (term172 A K k s f).
Proof. exact (@lem4404308 (term172 A K k s f)). Qed.
Lemma lem4404318 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term185 A K k s f) = (term172 A K k s f).
Proof. exact (TRANS (@lem4404306 A K k s f) (@lem4404309 A K k s f)). Qed.
Lemma lem4404319 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404320 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term186 A K k s f) = (term195 A K k s f).
Proof. exact (MK_COMB (@lem4404319) (@lem4404318 A K k s f)). Qed.
Lemma lem4404329 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term140 A K k s f) = (term140 A K k s f).
Proof. exact (eq_refl (term140 A K k s f)). Qed.
Lemma lem4404330 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term185 A K k s f) = (term140 A K k s f)) = ((term172 A K k s f) = (term140 A K k s f)).
Proof. exact (MK_COMB (@lem4404320 A K k s f) (@lem4404329 A K k s f)). Qed.
Lemma lem4404331 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term187 A K k s) = (term196 A K k s).
Proof. exact (fun_ext (fun f : K -> A => @lem4404330 A K k s f)). Qed.
Lemma lem4404332 {A K : Type'} : (@all (K -> A)) = (@all (K -> A)).
Proof. exact (eq_refl (@all (K -> A))). Qed.
Lemma lem4404333 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : (term188 A K k s) = (term197 A K k s).
Proof. exact (MK_COMB (@lem4404332 A K) (@lem4404331 A K k s)). Qed.
Lemma lem4404340 {A K : Type'} (k : K -> Prop) : (term189 A K k) = (term198 A K k).
Proof. exact (fun_ext (fun s : type1470 A K => @lem4404333 A K k s)). Qed.
Lemma lem4404341 {A K : Type'} : (@all (K -> A -> Prop)) = (@all (K -> A -> Prop)).
Proof. exact (eq_refl (@all (K -> A -> Prop))). Qed.
Lemma lem4404342 {A K : Type'} (k : K -> Prop) : (term190 A K k) = (term199 A K k).
Proof. exact (MK_COMB (@lem4404341 A K) (@lem4404340 A K k)). Qed.
Lemma lem4404349 {A K : Type'} : (term191 A K) = (term200 A K).
Proof. exact (fun_ext (fun k : K -> Prop => @lem4404342 A K k)). Qed.
Lemma lem4404350 {K : Type'} : (@all (K -> Prop)) = (@all (K -> Prop)).
Proof. exact (eq_refl (@all (K -> Prop))). Qed.
Lemma lem4404351 {A K : Type'} : (term192 A K) = (term201 A K).
Proof. exact (MK_COMB (@lem4404350 K) (@lem4404349 A K)). Qed.
Lemma lem4404358 {A K : Type'} : (term148 A K) = (term201 A K).
Proof. exact (TRANS (@lem4404270 A K) (@lem4404351 A K)). Qed.
Lemma lem4404359 {A K : Type'} : (term201 A K) = (term148 A K).
Proof. exact (SYM (@lem4404358 A K)). Qed.
Lemma lem4404361 (p : Prop) : p = (term147 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4404362 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term172 A K k s f) = (term140 A K k s f)) = (term202 A K k s f).
Proof. exact (@lem4404361 ((term172 A K k s f) = (term140 A K k s f))). Qed.
Lemma lem4404363 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term202 A K k s f) = ((term172 A K k s f) = (term140 A K k s f)).
Proof. exact (SYM (@lem4404362 A K k s f)). Qed.
Lemma lem4404364 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term203 A K k s f) : term203 A K k s f.
Proof. exact (h1). Qed.
Lemma lem4404368 {K : Type'} (k : K -> Prop) (i : K) : (term204 K k i) = (k i).
Proof. exact (@lem16933 (k i)). Qed.
Lemma lem4404369 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term205 A K s f i) = (term205 A K s f i).
Proof. exact (eq_refl (term205 A K s f i)). Qed.
Lemma lem4404371 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404372 {K : Type'} (k : K -> Prop) (i : K) : (term206 K k i) = (term207 K k i).
Proof. exact (MK_COMB (@lem4404371) (@lem4404368 K k i)). Qed.
Lemma lem4404373 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term208 A K k s f i) = (term209 A K k s f i).
Proof. exact (MK_COMB (@lem4404372 K k i) (@lem4404369 A K s f i)). Qed.
Lemma lem4404374 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term210 A K k s f i) = (term208 A K k s f i).
Proof. exact (@lem17160 (term114 K k i) (term135 A K s f i)). Qed.
Lemma lem4404375 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term210 A K k s f i) = (term209 A K k s f i).
Proof. exact (TRANS (@lem4404374 A K k s f i) (@lem4404373 A K k s f i)). Qed.
Lemma lem4404378 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term170 A K k s f i) = (term170 A K k s f i).
Proof. exact (eq_refl (term170 A K k s f i)). Qed.
Lemma lem4404379 {K : Type'} (P : K -> Prop) : (term211 K P) = (term212 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4404380 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term213 A K k s f) = (term214 A K k s f).
Proof. exact (@lem4404379 K (term171 A K k s f)). Qed.
Lemma lem4404381 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term215 A K k s f i) = (term170 A K k s f i).
Proof. exact (eq_refl (term215 A K k s f i)). Qed.
Lemma lem4404382 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4404383 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term216 A K k s f i) = (term210 A K k s f i).
Proof. exact (MK_COMB (@lem4404382) (@lem4404381 A K k s f i)). Qed.
Lemma lem4404384 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term216 A K k s f i) = (term209 A K k s f i).
Proof. exact (TRANS (@lem4404383 A K k s f i) (@lem4404375 A K k s f i)). Qed.
Lemma lem4404385 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term217 A K k s f) = (term218 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404384 A K k s f i)). Qed.
Lemma lem4404386 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404387 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term214 A K k s f) = (term219 A K k s f).
Proof. exact (MK_COMB (@lem4404386 K) (@lem4404385 A K k s f)). Qed.
Lemma lem4404388 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term213 A K k s f) = (term219 A K k s f).
Proof. exact (TRANS (@lem4404380 A K k s f) (@lem4404387 A K k s f)). Qed.
Lemma lem4404389 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term171 A K k s f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404378 A K k s f i)). Qed.
Lemma lem4404390 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404391 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404390 K) (@lem4404389 A K k s f)). Qed.
Lemma lem4404400 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term220 A K k s f i) = (term209 A K k s f i).
Proof. exact (@lem17362 (k i) (term135 A K s f i)). Qed.
Lemma lem4404405 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term137 A K k s f i) = (term170 A K k s f i).
Proof. exact (@lem17265 (k i) (term135 A K s f i)). Qed.
Lemma lem4404406 {K : Type'} (P : K -> Prop) : (term211 K P) = (term212 K P).
Proof. exact (@lem18392 K P). Qed.
Lemma lem4404407 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term221 A K k s f) = (term222 A K k s f).
Proof. exact (@lem4404406 K (term139 A K k s f)). Qed.
Lemma lem4404408 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term223 A K k s f i) = (term137 A K k s f i).
Proof. exact (eq_refl (term223 A K k s f i)). Qed.
Lemma lem4404409 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4404410 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term224 A K k s f i) = (term220 A K k s f i).
Proof. exact (MK_COMB (@lem4404409) (@lem4404408 A K k s f i)). Qed.
Lemma lem4404411 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term224 A K k s f i) = (term209 A K k s f i).
Proof. exact (TRANS (@lem4404410 A K k s f i) (@lem4404400 A K k s f i)). Qed.
Lemma lem4404412 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term225 A K k s f) = (term218 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404411 A K k s f i)). Qed.
Lemma lem4404413 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404414 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term222 A K k s f) = (term219 A K k s f).
Proof. exact (MK_COMB (@lem4404413 K) (@lem4404412 A K k s f)). Qed.
Lemma lem4404415 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term221 A K k s f) = (term219 A K k s f).
Proof. exact (TRANS (@lem4404407 A K k s f) (@lem4404414 A K k s f)). Qed.
Lemma lem4404416 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term139 A K k s f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404405 A K k s f i)). Qed.
Lemma lem4404417 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404418 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term140 A K k s f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404417 K) (@lem4404416 A K k s f)). Qed.
Lemma lem4404419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404420 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term226 A K k s f) = (term227 A K k s f).
Proof. exact (MK_COMB (@lem4404419) (@lem4404388 A K k s f)). Qed.
Lemma lem4404421 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term228 A K k s f) = (term229 A K k s f).
Proof. exact (MK_COMB (@lem4404420 A K k s f) (@lem4404418 A K k s f)). Qed.
Lemma lem4404422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404423 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term230 A K k s f) = (term230 A K k s f).
Proof. exact (MK_COMB (@lem4404422) (@lem4404391 A K k s f)). Qed.
Lemma lem4404424 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term231 A K k s f) = (term232 A K k s f).
Proof. exact (MK_COMB (@lem4404423 A K k s f) (@lem4404415 A K k s f)). Qed.
Lemma lem4404425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4404426 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term233 A K k s f) = (term234 A K k s f).
Proof. exact (MK_COMB (@lem4404425) (@lem4404424 A K k s f)). Qed.
Lemma lem4404427 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term235 A K k s f) = (term236 A K k s f).
Proof. exact (MK_COMB (@lem4404426 A K k s f) (@lem4404421 A K k s f)). Qed.
Lemma lem4404428 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term203 A K k s f) = (term235 A K k s f).
Proof. exact (@lem17646 (term172 A K k s f) (term140 A K k s f)). Qed.
Lemma lem4404429 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term203 A K k s f) = (term236 A K k s f).
Proof. exact (TRANS (@lem4404428 A K k s f) (@lem4404427 A K k s f)). Qed.
Lemma lem4404584 {A : Type'} (P : Prop) (Q : A -> Prop) : (term237 A P Q) = (term238 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4404585 {K : Type'} (P : Prop) (Q : K -> Prop) : (term237 K P Q) = (term238 K P Q).
Proof. exact (@lem4404584 K P Q). Qed.
Lemma lem4404586 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term239 A K k s f) = (term240 A K k s f).
Proof. exact (@lem4404585 K (term172 A K k s f) (term218 A K k s f)). Qed.
Lemma lem4404587 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term241 A K k s f i) = (term209 A K k s f i).
Proof. exact (eq_refl (term241 A K k s f i)). Qed.
Lemma lem4404588 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term242 A K k s f) = (term218 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404587 A K k s f i)). Qed.
Lemma lem4404589 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404590 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term243 A K k s f) = (term219 A K k s f).
Proof. exact (MK_COMB (@lem4404589 K) (@lem4404588 A K k s f)). Qed.
Lemma lem4404591 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term230 A K k s f) = (term230 A K k s f).
Proof. exact (eq_refl (term230 A K k s f)). Qed.
Lemma lem4404592 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term239 A K k s f) = (term232 A K k s f).
Proof. exact (MK_COMB (@lem4404591 A K k s f) (@lem4404590 A K k s f)). Qed.
Lemma lem4404593 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404594 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term244 A K k s f) = (term245 A K k s f).
Proof. exact (MK_COMB (@lem4404593) (@lem4404592 A K k s f)). Qed.
Lemma lem4404595 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term241 A K k s f i) = (term209 A K k s f i).
Proof. exact (eq_refl (term241 A K k s f i)). Qed.
Lemma lem4404596 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term230 A K k s f) = (term230 A K k s f).
Proof. exact (eq_refl (term230 A K k s f)). Qed.
Lemma lem4404597 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term246 A K k s f i) = (term247 A K k s f i).
Proof. exact (MK_COMB (@lem4404596 A K k s f) (@lem4404595 A K k s f i)). Qed.
Lemma lem4404598 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term248 A K k s f) = (term249 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404597 A K k s f i)). Qed.
Lemma lem4404599 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404600 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term240 A K k s f) = (term250 A K k s f).
Proof. exact (MK_COMB (@lem4404599 K) (@lem4404598 A K k s f)). Qed.
Lemma lem4404601 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term239 A K k s f) = (term240 A K k s f)) = ((term232 A K k s f) = (term250 A K k s f)).
Proof. exact (MK_COMB (@lem4404594 A K k s f) (@lem4404600 A K k s f)). Qed.
Lemma lem4404602 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term232 A K k s f) = (term250 A K k s f).
Proof. exact (EQ_MP (@lem4404601 A K k s f) (@lem4404586 A K k s f)). Qed.
Lemma lem4404603 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4404604 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term234 A K k s f) = (term251 A K k s f).
Proof. exact (MK_COMB (@lem4404603) (@lem4404602 A K k s f)). Qed.
Lemma lem4404606 {A : Type'} (P : A -> Prop) (Q : Prop) : (term252 A P Q) = (term253 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4404607 {K : Type'} (P : K -> Prop) (Q : Prop) : (term252 K P Q) = (term253 K P Q).
Proof. exact (@lem4404606 K P Q). Qed.
Lemma lem4404608 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term254 A K k s f) = (term255 A K k s f).
Proof. exact (@lem4404607 K (term218 A K k s f) (term172 A K k s f)). Qed.
Lemma lem4404609 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term241 A K k s f i) = (term209 A K k s f i).
Proof. exact (eq_refl (term241 A K k s f i)). Qed.
Lemma lem4404610 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term242 A K k s f) = (term218 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404609 A K k s f i)). Qed.
Lemma lem4404611 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404612 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term243 A K k s f) = (term219 A K k s f).
Proof. exact (MK_COMB (@lem4404611 K) (@lem4404610 A K k s f)). Qed.
Lemma lem4404613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404614 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term256 A K k s f) = (term227 A K k s f).
Proof. exact (MK_COMB (@lem4404613) (@lem4404612 A K k s f)). Qed.
Lemma lem4404615 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (eq_refl (term172 A K k s f)). Qed.
Lemma lem4404616 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term254 A K k s f) = (term229 A K k s f).
Proof. exact (MK_COMB (@lem4404614 A K k s f) (@lem4404615 A K k s f)). Qed.
Lemma lem4404617 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404618 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term257 A K k s f) = (term258 A K k s f).
Proof. exact (MK_COMB (@lem4404617) (@lem4404616 A K k s f)). Qed.
Lemma lem4404619 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term241 A K k s f i) = (term209 A K k s f i).
Proof. exact (eq_refl (term241 A K k s f i)). Qed.
Lemma lem4404620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404621 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term259 A K k s f i) = (term260 A K k s f i).
Proof. exact (MK_COMB (@lem4404620) (@lem4404619 A K k s f i)). Qed.
Lemma lem4404622 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (eq_refl (term172 A K k s f)). Qed.
Lemma lem4404623 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term261 A K i k s f) = (term262 A K i k s f).
Proof. exact (MK_COMB (@lem4404621 A K k s f i) (@lem4404622 A K k s f)). Qed.
Lemma lem4404624 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term263 A K k s f) = (term264 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404623 A K i k s f)). Qed.
Lemma lem4404625 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404626 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term255 A K k s f) = (term265 A K k s f).
Proof. exact (MK_COMB (@lem4404625 K) (@lem4404624 A K k s f)). Qed.
Lemma lem4404627 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term254 A K k s f) = (term255 A K k s f)) = ((term229 A K k s f) = (term265 A K k s f)).
Proof. exact (MK_COMB (@lem4404618 A K k s f) (@lem4404626 A K k s f)). Qed.
Lemma lem4404628 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term229 A K k s f) = (term265 A K k s f).
Proof. exact (EQ_MP (@lem4404627 A K k s f) (@lem4404608 A K k s f)). Qed.
Lemma lem4404629 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term236 A K k s f) = (term266 A K k s f).
Proof. exact (MK_COMB (@lem4404604 A K k s f) (@lem4404628 A K k s f)). Qed.
Lemma lem4404631 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term267 A P Q) = (term268 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4404632 {K : Type'} (P : K -> Prop) (Q : K -> Prop) : (term267 K P Q) = (term268 K P Q).
Proof. exact (@lem4404631 K P Q). Qed.
Lemma lem4404633 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term269 A K k s f) = (term270 A K k s f).
Proof. exact (@lem4404632 K (term249 A K k s f) (term264 A K k s f)). Qed.
Lemma lem4404634 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term271 A K k s f i) = (term247 A K k s f i).
Proof. exact (eq_refl (term271 A K k s f i)). Qed.
Lemma lem4404635 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term272 A K k s f) = (term249 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404634 A K k s f i)). Qed.
Lemma lem4404636 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404637 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term273 A K k s f) = (term250 A K k s f).
Proof. exact (MK_COMB (@lem4404636 K) (@lem4404635 A K k s f)). Qed.
Lemma lem4404638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4404639 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term274 A K k s f) = (term251 A K k s f).
Proof. exact (MK_COMB (@lem4404638) (@lem4404637 A K k s f)). Qed.
Lemma lem4404640 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term275 A K k s f i) = (term262 A K i k s f).
Proof. exact (eq_refl (term275 A K k s f i)). Qed.
Lemma lem4404641 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term276 A K k s f) = (term264 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404640 A K i k s f)). Qed.
Lemma lem4404642 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404643 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term277 A K k s f) = (term265 A K k s f).
Proof. exact (MK_COMB (@lem4404642 K) (@lem4404641 A K k s f)). Qed.
Lemma lem4404644 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term269 A K k s f) = (term266 A K k s f).
Proof. exact (MK_COMB (@lem4404639 A K k s f) (@lem4404643 A K k s f)). Qed.
Lemma lem4404645 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404646 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term278 A K k s f) = (term279 A K k s f).
Proof. exact (MK_COMB (@lem4404645) (@lem4404644 A K k s f)). Qed.
Lemma lem4404647 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term271 A K k s f i) = (term247 A K k s f i).
Proof. exact (eq_refl (term271 A K k s f i)). Qed.
Lemma lem4404648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4404649 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term280 A K k s f i) = (term281 A K k s f i).
Proof. exact (MK_COMB (@lem4404648) (@lem4404647 A K k s f i)). Qed.
Lemma lem4404650 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term275 A K k s f i) = (term262 A K i k s f).
Proof. exact (eq_refl (term275 A K k s f i)). Qed.
Lemma lem4404651 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term282 A K k s f i) = (term283 A K i k s f).
Proof. exact (MK_COMB (@lem4404649 A K k s f i) (@lem4404650 A K i k s f)). Qed.
Lemma lem4404652 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term284 A K k s f) = (term285 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404651 A K i k s f)). Qed.
Lemma lem4404653 {K : Type'} : (@ex K) = (@ex K).
Proof. exact (eq_refl (@ex K)). Qed.
Lemma lem4404654 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term270 A K k s f) = (term286 A K k s f).
Proof. exact (MK_COMB (@lem4404653 K) (@lem4404652 A K k s f)). Qed.
Lemma lem4404655 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : ((term269 A K k s f) = (term270 A K k s f)) = ((term266 A K k s f) = (term286 A K k s f)).
Proof. exact (MK_COMB (@lem4404646 A K k s f) (@lem4404654 A K k s f)). Qed.
Lemma lem4404656 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term266 A K k s f) = (term286 A K k s f).
Proof. exact (EQ_MP (@lem4404655 A K k s f) (@lem4404633 A K k s f)). Qed.
Lemma lem4404658 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term236 A K k s f) = (term286 A K k s f).
Proof. exact (TRANS (@lem4404629 A K k s f) (@lem4404656 A K k s f)). Qed.
Lemma lem4404659 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term203 A K k s f) = (term286 A K k s f).
Proof. exact (TRANS (@lem4404429 A K k s f) (@lem4404658 A K k s f)). Qed.
Lemma lem4404660 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term203 A K k s f) : term286 A K k s f.
Proof. exact (EQ_MP (@lem4404659 A K k s f) (@lem4404364 A K k s f h1)). Qed.
Lemma lem4404661 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term283 A K i k s f) : term283 A K i k s f.
Proof. exact (h1). Qed.
Lemma lem4404676 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term170 A K k s f i) = (term170 A K k s f i).
Proof. exact (eq_refl (term170 A K k s f i)). Qed.
Lemma lem4404677 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term171 A K k s f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404676 A K k s f i)). Qed.
Lemma lem4404678 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404679 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404678 K) (@lem4404677 A K k s f)). Qed.
Lemma lem4404696 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term260 A K k s f i) = (term260 A K k s f i).
Proof. exact (eq_refl (term260 A K k s f i)). Qed.
Lemma lem4404697 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term262 A K i k s f) = (term262 A K i k s f).
Proof. exact (MK_COMB (@lem4404696 A K k s f i) (@lem4404679 A K k s f)). Qed.
Lemma lem4404712 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term209 A K k s f i) = (term209 A K k s f i).
Proof. exact (eq_refl (term209 A K k s f i)). Qed.
Lemma lem4404727 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term170 A K k s f i) = (term170 A K k s f i).
Proof. exact (eq_refl (term170 A K k s f i)). Qed.
Lemma lem4404728 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term171 A K k s f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404727 A K k s f i)). Qed.
Lemma lem4404729 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404730 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404729 K) (@lem4404728 A K k s f)). Qed.
Lemma lem4404731 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4404732 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term230 A K k s f) = (term230 A K k s f).
Proof. exact (MK_COMB (@lem4404731) (@lem4404730 A K k s f)). Qed.
Lemma lem4404733 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term247 A K k s f i) = (term247 A K k s f i).
Proof. exact (MK_COMB (@lem4404732 A K k s f) (@lem4404712 A K k s f i)). Qed.
Lemma lem4404734 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4404735 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term281 A K k s f i) = (term281 A K k s f i).
Proof. exact (MK_COMB (@lem4404734) (@lem4404733 A K k s f i)). Qed.
Lemma lem4404736 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term283 A K i k s f) = (term283 A K i k s f).
Proof. exact (MK_COMB (@lem4404735 A K k s f i) (@lem4404697 A K i k s f)). Qed.
Lemma lem4404737 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term283 A K i k s f) : term283 A K i k s f.
Proof. exact (EQ_MP (@lem4404736 A K i k s f) (@lem4404661 A K i k s f h1)). Qed.
Lemma lem4404738 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term247 A K k s f i.
Proof. exact (h1). Qed.
Lemma lem4404739 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term262 A K i k s f.
Proof. exact (h1). Qed.
Lemma lem4404740 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term209 A K k s f i.
Proof. exact (proj2 (@lem4404738 A K k s f i h1)). Qed.
Lemma lem4404741 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term172 A K k s f.
Proof. exact (proj1 (@lem4404738 A K k s f i h1)). Qed.
Lemma lem4404744 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term172 A K k s f.
Proof. exact (proj2 (@lem4404739 A K i k s f h1)). Qed.
Lemma lem4404745 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term209 A K k s f i.
Proof. exact (proj1 (@lem4404739 A K i k s f h1)). Qed.
Lemma lem4404755 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term170 A K k s f i) = (term170 A K k s f i).
Proof. exact (eq_refl (term170 A K k s f i)). Qed.
Lemma lem4404756 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term171 A K k s f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404755 A K k s f i)). Qed.
Lemma lem4404757 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404759 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404757 K) (@lem4404756 A K k s f)). Qed.
Lemma lem4404760 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term172 A K k s f.
Proof. exact (EQ_MP (@lem4404759 A K k s f) (@lem4404741 A K k s f i h1)). Qed.
Lemma lem4404776 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) : (term170 A K k s f i) = (term170 A K k s f i).
Proof. exact (eq_refl (term170 A K k s f i)). Qed.
Lemma lem4404777 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term171 A K k s f) = (term171 A K k s f).
Proof. exact (fun_ext (fun i : K => @lem4404776 A K k s f i)). Qed.
Lemma lem4404778 {K : Type'} : (@all K) = (@all K).
Proof. exact (eq_refl (@all K)). Qed.
Lemma lem4404780 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term172 A K k s f).
Proof. exact (MK_COMB (@lem4404778 K) (@lem4404777 A K k s f)). Qed.
Lemma lem4404781 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term172 A K k s f.
Proof. exact (EQ_MP (@lem4404780 A K k s f) (@lem4404744 A K i k s f h1)). Qed.
Lemma lem4404790 {A K : Type'} (_50427 : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term215 A K k s f _50427.
Proof. exact (@lem4404760 A K k s f i h1 _50427). Qed.
Lemma lem4404791 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50427 : K) : (term215 A K k s f _50427) = (term170 A K k s f _50427).
Proof. exact (eq_refl (term215 A K k s f _50427)). Qed.
Lemma lem4404793 {A K : Type'} (_50428 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term215 A K k s f _50428.
Proof. exact (@lem4404781 A K i k s f h1 _50428). Qed.
Lemma lem4404794 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50428 : K) : (term215 A K k s f _50428) = (term170 A K k s f _50428).
Proof. exact (eq_refl (term215 A K k s f _50428)). Qed.
Lemma lem4404801 {A K : Type'} (_50427 : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term170 A K k s f _50427.
Proof. exact (EQ_MP (@lem4404791 A K k s f _50427) (@lem4404790 A K _50427 k s f i h1)). Qed.
Lemma lem4404805 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term205 A K s f i.
Proof. exact (proj2 (@lem4404740 A K k s f i h1)). Qed.
Lemma lem4404811 {A K : Type'} (_50428 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term170 A K k s f _50428.
Proof. exact (EQ_MP (@lem4404794 A K k s f _50428) (@lem4404793 A K _50428 i k s f h1)). Qed.
Lemma lem4404815 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term205 A K s f i.
Proof. exact (proj2 (@lem4404745 A K i k s f h1)). Qed.
Lemma lem4404817 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : k i.
Proof. exact (proj1 (@lem4404740 A K k s f i h1)). Qed.
Lemma lem4404818 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term287 K k i.
Proof. exact (fun h0 : term114 K k i => @lem4404817 A K k s f i h1). Qed.
Lemma lem4404820 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4404821 {K : Type'} (k : K -> Prop) (i : K) : (term287 K k i) = (k i).
Proof. exact (@lem4404820 (k i)). Qed.
Lemma lem4404822 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : k i.
Proof. exact (EQ_MP (@lem4404821 K k i) (@lem4404818 A K k s f i h1)). Qed.
Lemma lem4404828 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4404829 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : (term170 A K k s f _50427) = (term289 A K s f k _50427).
Proof. exact (@lem4404828 (term135 A K s f _50427) (term114 K k _50427)). Qed.
Lemma lem4404835 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404836 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : (term290 A K k s f _50427) = (term291 A K s f k _50427).
Proof. exact (MK_COMB (@lem4404835) (@lem4404829 A K s f k _50427)). Qed.
Lemma lem4404842 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : (term289 A K s f k _50427) = (term289 A K s f k _50427).
Proof. exact (eq_refl (term289 A K s f k _50427)). Qed.
Lemma lem4404843 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : ((term170 A K k s f _50427) = (term289 A K s f k _50427)) = ((term289 A K s f k _50427) = (term289 A K s f k _50427)).
Proof. exact (MK_COMB (@lem4404836 A K s f k _50427) (@lem4404842 A K s f k _50427)). Qed.
Lemma lem4404845 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4404846 (x : Prop) : (x = x) = True.
Proof. exact (@lem4404845 Prop x). Qed.
Lemma lem4404847 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : ((term289 A K s f k _50427) = (term289 A K s f k _50427)) = True.
Proof. exact (@lem4404846 (term289 A K s f k _50427)). Qed.
Lemma lem4404848 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : ((term170 A K k s f _50427) = (term289 A K s f k _50427)) = True.
Proof. exact (TRANS (@lem4404843 A K s f k _50427) (@lem4404847 A K s f k _50427)). Qed.
Lemma lem4404849 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : True = ((term170 A K k s f _50427) = (term289 A K s f k _50427)).
Proof. exact (SYM (@lem4404848 A K s f k _50427)). Qed.
Lemma lem4404850 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50427 : K) : (term170 A K k s f _50427) = (term289 A K s f k _50427).
Proof. exact (EQ_MP (@lem4404849 A K s f k _50427) (@lem0)). Qed.
Lemma lem4404851 {A K : Type'} (_50427 : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term289 A K s f k _50427.
Proof. exact (EQ_MP (@lem4404850 A K s f k _50427) (@lem4404801 A K _50427 k s f i h1)). Qed.
Lemma lem4404853 (b : Prop) (a : Prop) : (a \/ b) = (term292 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4404854 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50427 : K) : (term289 A K s f k _50427) = (term293 A K k s f _50427).
Proof. exact (@lem4404853 (term114 K k _50427) (term135 A K s f _50427)). Qed.
Lemma lem4404856 (a : Prop) : (term154 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4404857 {K : Type'} (k : K -> Prop) (_50427 : K) : (term204 K k _50427) = (k _50427).
Proof. exact (@lem4404856 (k _50427)). Qed.
Lemma lem4404858 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4404859 {K : Type'} (k : K -> Prop) (_50427 : K) : (term294 K k _50427) = (term126 K k _50427).
Proof. exact (MK_COMB (@lem4404858) (@lem4404857 K k _50427)). Qed.
Lemma lem4404860 {A K : Type'} (s : type1470 A K) (f : K -> A) (_50427 : K) : (term135 A K s f _50427) = (term135 A K s f _50427).
Proof. exact (eq_refl (term135 A K s f _50427)). Qed.
Lemma lem4404861 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50427 : K) : (term293 A K k s f _50427) = (term137 A K k s f _50427).
Proof. exact (MK_COMB (@lem4404859 K k _50427) (@lem4404860 A K s f _50427)). Qed.
Lemma lem4404862 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50427 : K) : (term289 A K s f k _50427) = (term137 A K k s f _50427).
Proof. exact (TRANS (@lem4404854 A K k s f _50427) (@lem4404861 A K k s f _50427)). Qed.
Lemma lem4404865 {A K : Type'} (_50427 : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term137 A K k s f _50427.
Proof. exact (EQ_MP (@lem4404862 A K k s f _50427) (@lem4404851 A K _50427 k s f i h1)). Qed.
Lemma lem4404866 {A K : Type'} (_50427 : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term137 A K k s f _50427.
Proof. exact (@lem4404865 A K _50427 k s f i h1). Qed.
Lemma lem4404867 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term137 A K k s f i.
Proof. exact (@lem4404866 A K i k s f i h1). Qed.
Lemma lem4404870 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term135 A K s f i.
Proof. exact (@lem4404867 A K k s f i h1 (@lem4404822 A K k s f i h1)). Qed.
Lemma lem4404871 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term295 A K s f i.
Proof. exact (fun h0 : term205 A K s f i => @lem4404870 A K k s f i h1). Qed.
Lemma lem4404873 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4404874 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term295 A K s f i) = (term135 A K s f i).
Proof. exact (@lem4404873 (term135 A K s f i)). Qed.
Lemma lem4404875 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term135 A K s f i.
Proof. exact (EQ_MP (@lem4404874 A K s f i) (@lem4404871 A K k s f i h1)). Qed.
Lemma lem4404878 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4404880 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term205 A K s f i) = (term296 A K s f i).
Proof. exact (@lem4404878 (term135 A K s f i)). Qed.
Lemma lem4404883 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term296 A K s f i.
Proof. exact (EQ_MP (@lem4404880 A K s f i) (@lem4404805 A K k s f i h1)). Qed.
Lemma lem4404886 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : False.
Proof. exact (@lem4404883 A K k s f i h1 (@lem4404875 A K k s f i h1)). Qed.
Lemma lem4404887 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : term297.
Proof. exact (fun h0 : ~ False => @lem4404886 A K k s f i h1). Qed.
Lemma lem4404889 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4404890 : term297 = False.
Proof. exact (@lem4404889 False). Qed.
Lemma lem4404891 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (i : K) (h1 : term247 A K k s f i) : False.
Proof. exact (EQ_MP (@lem4404890) (@lem4404887 A K k s f i h1)). Qed.
Lemma lem4404893 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : k i.
Proof. exact (proj1 (@lem4404745 A K i k s f h1)). Qed.
Lemma lem4404894 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term287 K k i.
Proof. exact (fun h0 : term114 K k i => @lem4404893 A K i k s f h1). Qed.
Lemma lem4404896 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4404897 {K : Type'} (k : K -> Prop) (i : K) : (term287 K k i) = (k i).
Proof. exact (@lem4404896 (k i)). Qed.
Lemma lem4404898 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : k i.
Proof. exact (EQ_MP (@lem4404897 K k i) (@lem4404894 A K i k s f h1)). Qed.
Lemma lem4404904 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4404905 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : (term170 A K k s f _50428) = (term289 A K s f k _50428).
Proof. exact (@lem4404904 (term135 A K s f _50428) (term114 K k _50428)). Qed.
Lemma lem4404911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4404912 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : (term290 A K k s f _50428) = (term291 A K s f k _50428).
Proof. exact (MK_COMB (@lem4404911) (@lem4404905 A K s f k _50428)). Qed.
Lemma lem4404918 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : (term289 A K s f k _50428) = (term289 A K s f k _50428).
Proof. exact (eq_refl (term289 A K s f k _50428)). Qed.
Lemma lem4404919 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : ((term170 A K k s f _50428) = (term289 A K s f k _50428)) = ((term289 A K s f k _50428) = (term289 A K s f k _50428)).
Proof. exact (MK_COMB (@lem4404912 A K s f k _50428) (@lem4404918 A K s f k _50428)). Qed.
Lemma lem4404921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4404922 (x : Prop) : (x = x) = True.
Proof. exact (@lem4404921 Prop x). Qed.
Lemma lem4404923 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : ((term289 A K s f k _50428) = (term289 A K s f k _50428)) = True.
Proof. exact (@lem4404922 (term289 A K s f k _50428)). Qed.
Lemma lem4404924 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : ((term170 A K k s f _50428) = (term289 A K s f k _50428)) = True.
Proof. exact (TRANS (@lem4404919 A K s f k _50428) (@lem4404923 A K s f k _50428)). Qed.
Lemma lem4404925 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : True = ((term170 A K k s f _50428) = (term289 A K s f k _50428)).
Proof. exact (SYM (@lem4404924 A K s f k _50428)). Qed.
Lemma lem4404926 {A K : Type'} (s : type1470 A K) (f : K -> A) (k : K -> Prop) (_50428 : K) : (term170 A K k s f _50428) = (term289 A K s f k _50428).
Proof. exact (EQ_MP (@lem4404925 A K s f k _50428) (@lem0)). Qed.
Lemma lem4404927 {A K : Type'} (_50428 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term289 A K s f k _50428.
Proof. exact (EQ_MP (@lem4404926 A K s f k _50428) (@lem4404811 A K _50428 i k s f h1)). Qed.
Lemma lem4404929 (b : Prop) (a : Prop) : (a \/ b) = (term292 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4404930 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50428 : K) : (term289 A K s f k _50428) = (term293 A K k s f _50428).
Proof. exact (@lem4404929 (term114 K k _50428) (term135 A K s f _50428)). Qed.
Lemma lem4404932 (a : Prop) : (term154 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4404933 {K : Type'} (k : K -> Prop) (_50428 : K) : (term204 K k _50428) = (k _50428).
Proof. exact (@lem4404932 (k _50428)). Qed.
Lemma lem4404934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4404935 {K : Type'} (k : K -> Prop) (_50428 : K) : (term294 K k _50428) = (term126 K k _50428).
Proof. exact (MK_COMB (@lem4404934) (@lem4404933 K k _50428)). Qed.
Lemma lem4404936 {A K : Type'} (s : type1470 A K) (f : K -> A) (_50428 : K) : (term135 A K s f _50428) = (term135 A K s f _50428).
Proof. exact (eq_refl (term135 A K s f _50428)). Qed.
Lemma lem4404937 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50428 : K) : (term293 A K k s f _50428) = (term137 A K k s f _50428).
Proof. exact (MK_COMB (@lem4404935 K k _50428) (@lem4404936 A K s f _50428)). Qed.
Lemma lem4404938 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (_50428 : K) : (term289 A K s f k _50428) = (term137 A K k s f _50428).
Proof. exact (TRANS (@lem4404930 A K k s f _50428) (@lem4404937 A K k s f _50428)). Qed.
Lemma lem4404941 {A K : Type'} (_50428 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term137 A K k s f _50428.
Proof. exact (EQ_MP (@lem4404938 A K k s f _50428) (@lem4404927 A K _50428 i k s f h1)). Qed.
Lemma lem4404942 {A K : Type'} (_50428 : K) (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term137 A K k s f _50428.
Proof. exact (@lem4404941 A K _50428 i k s f h1). Qed.
Lemma lem4404943 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term137 A K k s f i.
Proof. exact (@lem4404942 A K i i k s f h1). Qed.
Lemma lem4404946 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term135 A K s f i.
Proof. exact (@lem4404943 A K i k s f h1 (@lem4404898 A K i k s f h1)). Qed.
Lemma lem4404947 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term295 A K s f i.
Proof. exact (fun h0 : term205 A K s f i => @lem4404946 A K i k s f h1). Qed.
Lemma lem4404949 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4404950 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term295 A K s f i) = (term135 A K s f i).
Proof. exact (@lem4404949 (term135 A K s f i)). Qed.
Lemma lem4404951 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term135 A K s f i.
Proof. exact (EQ_MP (@lem4404950 A K s f i) (@lem4404947 A K i k s f h1)). Qed.
Lemma lem4404954 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4404956 {A K : Type'} (s : type1470 A K) (f : K -> A) (i : K) : (term205 A K s f i) = (term296 A K s f i).
Proof. exact (@lem4404954 (term135 A K s f i)). Qed.
Lemma lem4404959 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term296 A K s f i.
Proof. exact (EQ_MP (@lem4404956 A K s f i) (@lem4404815 A K i k s f h1)). Qed.
Lemma lem4404962 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : False.
Proof. exact (@lem4404959 A K i k s f h1 (@lem4404951 A K i k s f h1)). Qed.
Lemma lem4404963 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : term297.
Proof. exact (fun h0 : ~ False => @lem4404962 A K i k s f h1). Qed.
Lemma lem4404965 (p : Prop) : (term288 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4404966 : term297 = False.
Proof. exact (@lem4404965 False). Qed.
Lemma lem4404967 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term262 A K i k s f) : False.
Proof. exact (EQ_MP (@lem4404966) (@lem4404963 A K i k s f h1)). Qed.
Lemma lem4404968 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term283 A K i k s f) : False.
Proof. exact (or_elim (@lem4404737 A K i k s f h1) (fun h0 : term247 A K k s f i => @lem4404891 A K k s f i h0) (fun h0 : term262 A K i k s f => @lem4404967 A K i k s f h0)). Qed.
Lemma lem4404969 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term283 A K i k s f) : (term283 A K i k s f) = False.
Proof. exact (prop_ext (fun h2 : term283 A K i k s f => @lem4404968 A K i k s f h1) (fun h2 : False => @lem4404737 A K i k s f h1)). Qed.
Lemma lem4404970 {A K : Type'} (i : K) (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term283 A K i k s f) : False.
Proof. exact (EQ_MP (@lem4404969 A K i k s f h1) (@lem4404737 A K i k s f h1)). Qed.
Lemma lem4404971 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term203 A K k s f) : False.
Proof. exact (ex_elim (@lem4404660 A K k s f h1) (fun i : K => fun h0 : term285 A K k s f i => @lem4404970 A K i k s f h0)). Qed.
Lemma lem4404972 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term203 A K k s f) : (term203 A K k s f) = False.
Proof. exact (prop_ext (fun h2 : term203 A K k s f => @lem4404971 A K k s f h1) (fun h2 : False => @lem4404364 A K k s f h1)). Qed.
Lemma lem4404973 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) (h1 : term203 A K k s f) : False.
Proof. exact (EQ_MP (@lem4404972 A K k s f h1) (@lem4404364 A K k s f h1)). Qed.
Lemma lem4404974 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : term202 A K k s f.
Proof. exact (fun h0 : term203 A K k s f => @lem4404973 A K k s f h0). Qed.
Lemma lem4404975 {A K : Type'} (k : K -> Prop) (s : type1470 A K) (f : K -> A) : (term172 A K k s f) = (term140 A K k s f).
Proof. exact (EQ_MP (@lem4404363 A K k s f) (@lem4404974 A K k s f)). Qed.
Lemma lem4404980 {A K : Type'} (k : K -> Prop) (s : type1470 A K) : term197 A K k s.
Proof. exact (fun f : K -> A => @lem4404975 A K k s f). Qed.
Lemma lem4404985 {A K : Type'} (k : K -> Prop) : term199 A K k.
Proof. exact (fun s : type1470 A K => @lem4404980 A K k s). Qed.
Lemma lem4404990 {A K : Type'} : term201 A K.
Proof. exact (fun k : K -> Prop => @lem4404985 A K k). Qed.
Lemma lem4404991 {A K : Type'} : term148 A K.
Proof. exact (EQ_MP (@lem4404359 A K) (@lem4404990 A K)). Qed.
Lemma lem4404993 {A K : Type'} : term148 A K.
Proof. exact (@lem4404020 A K (@lem4404991 A K)). Qed.
Lemma lem4404994 {A K : Type'} (h1 : term149 A K) : False.
Proof. exact (@lem4404993 A K (@lem4404004 A K h1)). Qed.
Lemma lem4404995 {A K : Type'} (h1 : term149 A K) : (term149 A K) = False.
Proof. exact (prop_ext (fun h2 : term149 A K => @lem4404994 A K h1) (fun h2 : False => @lem4404004 A K h1)). Qed.
Lemma lem4404996 {A K : Type'} (h1 : term149 A K) : False.
Proof. exact (EQ_MP (@lem4404995 A K h1) (@lem4404004 A K h1)). Qed.
Lemma lem4404997 {A K : Type'} : term148 A K.
Proof. exact (fun h0 : term149 A K => @lem4404996 A K h0). Qed.
Lemma lem4404998 {A K : Type'} : term146 A K.
Proof. exact (EQ_MP (@lem4404003 A K) (@lem4404997 A K)). Qed.
Lemma lem4405000 {A K : Type'} : term112 A K.
Proof. exact (EQ_MP (@lem4403999 A K) (@lem4404998 A K)). Qed.
Lemma lem4405001 {A K : Type'} : term111 A K.
Proof. exact (EQ_MP (@lem4403802 A K) (@lem4405000 A K)). Qed.
