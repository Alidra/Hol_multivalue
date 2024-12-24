Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL2_MAP2_term_abbrevs.
Require Import ALL2_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1163658 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1163659 {_27382 : Type'} (P : type1143 _27382) : term0 _27382 P.
Proof. exact (@lem1163658 _27382 P). Qed.
Lemma lem1163660 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term1 _27380 _27381 _27382 _27383 P f g.
Proof. exact (@lem1163659 _27382 (term2 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163661 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term3 _27380 _27381 _27382 _27383 P f g) = (term4 _27380 _27381 _27382 _27383 P f g).
Proof. exact (eq_refl (term3 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1163663 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term5 _27380 _27381 _27382 _27383 P f g) = (term6 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163662) (@lem1163661 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163664 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) : (term7 _27380 _27381 _27382 _27383 P f g t) = (term8 _27380 _27381 _27382 _27383 P f g t).
Proof. exact (eq_refl (term7 _27380 _27381 _27382 _27383 P f g t)). Qed.
Lemma lem1163665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163666 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) : (term9 _27380 _27381 _27382 _27383 P f g t) = (term10 _27380 _27381 _27382 _27383 P f g t).
Proof. exact (MK_COMB (@lem1163665) (@lem1163664 _27380 _27381 _27382 _27383 P f g t)). Qed.
Lemma lem1163667 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term11 _27380 _27381 _27382 _27383 P f g h t) = (term12 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (eq_refl (term11 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163668 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term13 _27380 _27381 _27382 _27383 P f g h t) = (term14 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163666 _27380 _27381 _27382 _27383 P f g t) (@lem1163667 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163669 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) : (term15 _27380 _27381 _27382 _27383 P f g h) = (term16 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (fun_ext (fun t : list _27382 => @lem1163668 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163670 {_27382 : Type'} : (@all (list _27382)) = (@all (list _27382)).
Proof. exact (eq_refl (@all (list _27382))). Qed.
Lemma lem1163671 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) : (term17 _27380 _27381 _27382 _27383 P f g h) = (term18 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (MK_COMB (@lem1163670 _27382) (@lem1163669 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163672 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term19 _27380 _27381 _27382 _27383 P f g) = (term20 _27380 _27381 _27382 _27383 P f g).
Proof. exact (fun_ext (fun h : _27382 => @lem1163671 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163673 {_27382 : Type'} : (@all _27382) = (@all _27382).
Proof. exact (eq_refl (@all _27382)). Qed.
Lemma lem1163674 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term21 _27380 _27381 _27382 _27383 P f g) = (term22 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163673 _27382) (@lem1163672 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163675 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term23 _27380 _27381 _27382 _27383 P f g) = (term24 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163663 _27380 _27381 _27382 _27383 P f g) (@lem1163674 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163676 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163677 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term25 _27380 _27381 _27382 _27383 P f g) = (term26 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163676) (@lem1163675 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163678 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (l : list _27382) : (term7 _27380 _27381 _27382 _27383 P f g l) = (term8 _27380 _27381 _27382 _27383 P f g l).
Proof. exact (eq_refl (term7 _27380 _27381 _27382 _27383 P f g l)). Qed.
Lemma lem1163679 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term27 _27380 _27381 _27382 _27383 P f g) = (term2 _27380 _27381 _27382 _27383 P f g).
Proof. exact (fun_ext (fun l : list _27382 => @lem1163678 _27380 _27381 _27382 _27383 P f g l)). Qed.
Lemma lem1163680 {_27382 : Type'} : (@all (list _27382)) = (@all (list _27382)).
Proof. exact (eq_refl (@all (list _27382))). Qed.
Lemma lem1163681 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term28 _27380 _27381 _27382 _27383 P f g) = (term29 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163680 _27382) (@lem1163679 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163682 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term1 _27380 _27381 _27382 _27383 P f g) = (term30 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163677 _27380 _27381 _27382 _27383 P f g) (@lem1163681 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163683 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term30 _27380 _27381 _27382 _27383 P f g.
Proof. exact (EQ_MP (@lem1163682 _27380 _27381 _27382 _27383 P f g) (@lem1163660 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163684 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term8 _27380 _27381 _27382 _27383 P f g t.
Proof. exact (h1). Qed.
Lemma lem1163686 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1163687 {_27383 : Type'} (P : type1143 _27383) : term0 _27383 P.
Proof. exact (@lem1163686 _27383 P). Qed.
Lemma lem1163688 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term31 _27380 _27381 _27382 _27383 P f g.
Proof. exact (@lem1163687 _27383 (term32 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163689 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term33 _27380 _27381 _27382 _27383 P f g) = ((term34 _27380 _27381 _27382 _27383 P f g) = (term35 _27380 _27381 _27382 _27383 P f g)).
Proof. exact (eq_refl (term33 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1163691 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term36 _27380 _27381 _27382 _27383 P f g) = (term37 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163690) (@lem1163689 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163692 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27383) : (term38 _27380 _27381 _27382 _27383 P f g t) = ((term39 _27380 _27381 _27382 _27383 P f g t) = (term40 _27380 _27381 _27382 _27383 P f g t)).
Proof. exact (eq_refl (term38 _27380 _27381 _27382 _27383 P f g t)). Qed.
Lemma lem1163693 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163694 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27383) : (term41 _27380 _27381 _27382 _27383 P f g t) = (term42 _27380 _27381 _27382 _27383 P f g t).
Proof. exact (MK_COMB (@lem1163693) (@lem1163692 _27380 _27381 _27382 _27383 P f g t)). Qed.
Lemma lem1163695 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : (term43 _27380 _27381 _27382 _27383 P f g h t) = ((term44 _27380 _27381 _27382 _27383 P f g h t) = (term45 _27380 _27381 _27382 _27383 P f g h t)).
Proof. exact (eq_refl (term43 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163696 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : (term46 _27380 _27381 _27382 _27383 P f g h t) = (term47 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163694 _27380 _27381 _27382 _27383 P f g t) (@lem1163695 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163697 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) : (term48 _27380 _27381 _27382 _27383 P f g h) = (term49 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (fun_ext (fun t : list _27383 => @lem1163696 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163698 {_27383 : Type'} : (@all (list _27383)) = (@all (list _27383)).
Proof. exact (eq_refl (@all (list _27383))). Qed.
Lemma lem1163699 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) : (term50 _27380 _27381 _27382 _27383 P f g h) = (term51 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (MK_COMB (@lem1163698 _27383) (@lem1163697 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163700 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term52 _27380 _27381 _27382 _27383 P f g) = (term53 _27380 _27381 _27382 _27383 P f g).
Proof. exact (fun_ext (fun h : _27383 => @lem1163699 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163701 {_27383 : Type'} : (@all _27383) = (@all _27383).
Proof. exact (eq_refl (@all _27383)). Qed.
Lemma lem1163702 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term54 _27380 _27381 _27382 _27383 P f g) = (term55 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163701 _27383) (@lem1163700 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163703 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term56 _27380 _27381 _27382 _27383 P f g) = (term57 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163691 _27380 _27381 _27382 _27383 P f g) (@lem1163702 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163705 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term58 _27380 _27381 _27382 _27383 P f g) = (term59 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163704) (@lem1163703 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163706 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (m : list _27383) : (term38 _27380 _27381 _27382 _27383 P f g m) = ((term39 _27380 _27381 _27382 _27383 P f g m) = (term40 _27380 _27381 _27382 _27383 P f g m)).
Proof. exact (eq_refl (term38 _27380 _27381 _27382 _27383 P f g m)). Qed.
Lemma lem1163707 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term60 _27380 _27381 _27382 _27383 P f g) = (term32 _27380 _27381 _27382 _27383 P f g).
Proof. exact (fun_ext (fun m : list _27383 => @lem1163706 _27380 _27381 _27382 _27383 P f g m)). Qed.
Lemma lem1163708 {_27383 : Type'} : (@all (list _27383)) = (@all (list _27383)).
Proof. exact (eq_refl (@all (list _27383))). Qed.
Lemma lem1163709 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term61 _27380 _27381 _27382 _27383 P f g) = (term4 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163708 _27383) (@lem1163707 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163710 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term31 _27380 _27381 _27382 _27383 P f g) = (term62 _27380 _27381 _27382 _27383 P f g).
Proof. exact (MK_COMB (@lem1163705 _27380 _27381 _27382 _27383 P f g) (@lem1163709 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163711 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term62 _27380 _27381 _27382 _27383 P f g.
Proof. exact (EQ_MP (@lem1163710 _27380 _27381 _27382 _27383 P f g) (@lem1163688 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163714 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1163715 {_27383 : Type'} (P : type1143 _27383) : term0 _27383 P.
Proof. exact (@lem1163714 _27383 P). Qed.
Lemma lem1163716 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : term63 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (@lem1163715 _27383 (term64 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163717 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term65 _27380 _27381 _27382 _27383 P f g h t) = ((term66 _27380 _27381 _27382 _27383 P f h t g) = (term67 _27380 _27381 _27382 _27383 P f g h t)).
Proof. exact (eq_refl (term65 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163718 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1163719 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term68 _27380 _27381 _27382 _27383 P f g h t) = (term69 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163718) (@lem1163717 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163720 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (t' : list _27383) : (term70 _27380 _27381 _27382 _27383 P f g h t t') = ((term71 _27380 _27381 _27382 _27383 P f h t g t') = (term72 _27380 _27381 _27382 _27383 P f g h t t')).
Proof. exact (eq_refl (term70 _27380 _27381 _27382 _27383 P f g h t t')). Qed.
Lemma lem1163721 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163722 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (t' : list _27383) : (term73 _27380 _27381 _27382 _27383 P f g h t t') = (term74 _27380 _27381 _27382 _27383 P f g h t t').
Proof. exact (MK_COMB (@lem1163721) (@lem1163720 _27380 _27381 _27382 _27383 P f g h t t')). Qed.
Lemma lem1163723 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (h' : _27383) (t' : list _27383) : (term75 _27380 _27381 _27382 _27383 P f g h t h' t') = ((term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term77 _27380 _27381 _27382 _27383 P f g h t h' t')).
Proof. exact (eq_refl (term75 _27380 _27381 _27382 _27383 P f g h t h' t')). Qed.
Lemma lem1163724 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (h' : _27383) (t' : list _27383) : (term78 _27380 _27381 _27382 _27383 P f g h t h' t') = (term79 _27380 _27381 _27382 _27383 P f g h t h' t').
Proof. exact (MK_COMB (@lem1163722 _27380 _27381 _27382 _27383 P f g h t t') (@lem1163723 _27380 _27381 _27382 _27383 P f g h t h' t')). Qed.
Lemma lem1163725 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (h' : _27383) : (term80 _27380 _27381 _27382 _27383 P f g h t h') = (term81 _27380 _27381 _27382 _27383 P f g h t h').
Proof. exact (fun_ext (fun t' : list _27383 => @lem1163724 _27380 _27381 _27382 _27383 P f g h t h' t')). Qed.
Lemma lem1163726 {_27383 : Type'} : (@all (list _27383)) = (@all (list _27383)).
Proof. exact (eq_refl (@all (list _27383))). Qed.
Lemma lem1163727 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (h' : _27383) : (term82 _27380 _27381 _27382 _27383 P f g h t h') = (term83 _27380 _27381 _27382 _27383 P f g h t h').
Proof. exact (MK_COMB (@lem1163726 _27383) (@lem1163725 _27380 _27381 _27382 _27383 P f g h t h')). Qed.
Lemma lem1163728 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term84 _27380 _27381 _27382 _27383 P f g h t) = (term85 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (fun_ext (fun h' : _27383 => @lem1163727 _27380 _27381 _27382 _27383 P f g h t h')). Qed.
Lemma lem1163729 {_27383 : Type'} : (@all _27383) = (@all _27383).
Proof. exact (eq_refl (@all _27383)). Qed.
Lemma lem1163730 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term86 _27380 _27381 _27382 _27383 P f g h t) = (term87 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163729 _27383) (@lem1163728 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163731 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term88 _27380 _27381 _27382 _27383 P f g h t) = (term89 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163719 _27380 _27381 _27382 _27383 P f g h t) (@lem1163730 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1163733 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term90 _27380 _27381 _27382 _27383 P f g h t) = (term91 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163732) (@lem1163731 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163734 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) (m : list _27383) : (term70 _27380 _27381 _27382 _27383 P f g h t m) = ((term71 _27380 _27381 _27382 _27383 P f h t g m) = (term72 _27380 _27381 _27382 _27383 P f g h t m)).
Proof. exact (eq_refl (term70 _27380 _27381 _27382 _27383 P f g h t m)). Qed.
Lemma lem1163735 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term92 _27380 _27381 _27382 _27383 P f g h t) = (term64 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (fun_ext (fun m : list _27383 => @lem1163734 _27380 _27381 _27382 _27383 P f g h t m)). Qed.
Lemma lem1163736 {_27383 : Type'} : (@all (list _27383)) = (@all (list _27383)).
Proof. exact (eq_refl (@all (list _27383))). Qed.
Lemma lem1163737 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term93 _27380 _27381 _27382 _27383 P f g h t) = (term12 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163736 _27383) (@lem1163735 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163738 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term63 _27380 _27381 _27382 _27383 P f g h t) = (term94 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (MK_COMB (@lem1163733 _27380 _27381 _27382 _27383 P f g h t) (@lem1163737 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163739 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : term94 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (EQ_MP (@lem1163738 _27380 _27381 _27382 _27383 P f g h t) (@lem1163716 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163751 {A B : Type'} : term95 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1163752 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (@lem1163751 A B f). Qed.
Lemma lem1163753 {A B : Type'} (f : A -> B) : (term96 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term96 A B f)). Qed.
Lemma lem1163764 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1163753 A B f) (@lem1163752 A B f)). Qed.
Lemma lem1163765 {_27381 _27382 : Type'} (f : _27382 -> _27381) : (@List.map _27382 _27381 f (@nil _27382)) = (@nil _27381).
Proof. exact (@lem1163764 _27382 _27381 f). Qed.
Lemma lem1163766 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) : (@ALL2 _27381 _27380 P) = (@ALL2 _27381 _27380 P).
Proof. exact (eq_refl (@ALL2 _27381 _27380 P)). Qed.
Lemma lem1163767 {_27380 _27381 _27382 : Type'} (f : _27382 -> _27381) (P : type1470 _27380 _27381) : (term97 _27380 _27381 _27382 P f) = (@ALL2 _27381 _27380 P (@nil _27381)).
Proof. exact (MK_COMB (@lem1163766 _27380 _27381 P) (@lem1163765 _27381 _27382 f)). Qed.
Lemma lem1163769 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1163753 A B f) (@lem1163752 A B f)). Qed.
Lemma lem1163770 {_27380 _27383 : Type'} (f : _27383 -> _27380) : (@List.map _27383 _27380 f (@nil _27383)) = (@nil _27380).
Proof. exact (@lem1163769 _27383 _27380 f). Qed.
Lemma lem1163771 {_27380 _27383 : Type'} (g : _27383 -> _27380) : (@List.map _27383 _27380 g (@nil _27383)) = (@nil _27380).
Proof. exact (@lem1163770 _27380 _27383 g). Qed.
Lemma lem1163772 {_27380 _27381 _27382 _27383 : Type'} (f : _27382 -> _27381) (g : _27383 -> _27380) (P : type1470 _27380 _27381) : (term34 _27380 _27381 _27382 _27383 P f g) = (@ALL2 _27381 _27380 P (@nil _27381) (@nil _27380)).
Proof. exact (MK_COMB (@lem1163767 _27380 _27381 _27382 f P) (@lem1163771 _27380 _27383 g)). Qed.
Lemma lem1163774 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1163775 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) : (@ALL2 _27381 _27380 P (@nil _27381) (@nil _27380)) = True.
Proof. exact (@lem1163774 _27380 _27381 P). Qed.
Lemma lem1163776 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term34 _27380 _27381 _27382 _27383 P f g) = True.
Proof. exact (TRANS (@lem1163772 _27380 _27381 _27382 _27383 f g P) (@lem1163775 _27380 _27381 P)). Qed.
Lemma lem1163777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163778 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term98 _27380 _27381 _27382 _27383 P f g) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1163777) (@lem1163776 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163780 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1163781 {_27382 _27383 : Type'} (P : type1413 _27382 _27383) : (@ALL2 _27382 _27383 P (@nil _27382) (@nil _27383)) = True.
Proof. exact (@lem1163780 _27383 _27382 P). Qed.
Lemma lem1163782 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term35 _27380 _27381 _27382 _27383 P f g) = True.
Proof. exact (@lem1163781 _27382 _27383 (term99 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163783 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : ((term34 _27380 _27381 _27382 _27383 P f g) = (term35 _27380 _27381 _27382 _27383 P f g)) = (True = True).
Proof. exact (MK_COMB (@lem1163778 _27380 _27381 _27382 _27383 P f g) (@lem1163782 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163785 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1163786 : (True = True) = True.
Proof. exact (@lem1163785 True). Qed.
Lemma lem1163787 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : ((term34 _27380 _27381 _27382 _27383 P f g) = (term35 _27380 _27381 _27382 _27383 P f g)) = True.
Proof. exact (TRANS (@lem1163783 _27380 _27381 _27382 _27383 P f g) (@lem1163786)). Qed.
Lemma lem1163788 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : True = ((term34 _27380 _27381 _27382 _27383 P f g) = (term35 _27380 _27381 _27382 _27383 P f g)).
Proof. exact (SYM (@lem1163787 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1163789 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term34 _27380 _27381 _27382 _27383 P f g) = (term35 _27380 _27381 _27382 _27383 P f g).
Proof. exact (EQ_MP (@lem1163788 _27380 _27381 _27382 _27383 P f g) (@lem0)). Qed.
Lemma lem1163790 {A B : Type'} : term100 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1163791 {A B : Type'} (f : A -> B) : term101 A B f.
Proof. exact (@lem1163790 A B f). Qed.
Lemma lem1163792 {A B : Type'} (f : A -> B) : (term101 A B f) = (term102 A B f).
Proof. exact (eq_refl (term101 A B f)). Qed.
Lemma lem1163793 {A B : Type'} (f : A -> B) : term102 A B f.
Proof. exact (EQ_MP (@lem1163792 A B f) (@lem1163791 A B f)). Qed.
Lemma lem1163794 {A B : Type'} (f : A -> B) (h : A) : term103 A B f h.
Proof. exact (@lem1163793 A B f h). Qed.
Lemma lem1163795 {A B : Type'} (h : A) (f : A -> B) : (term103 A B f h) = (term104 A B h f).
Proof. exact (eq_refl (term103 A B f h)). Qed.
Lemma lem1163796 {A B : Type'} (h : A) (f : A -> B) : term104 A B h f.
Proof. exact (EQ_MP (@lem1163795 A B h f) (@lem1163794 A B f h)). Qed.
Lemma lem1163797 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term105 A B h f t.
Proof. exact (@lem1163796 A B h f t). Qed.
Lemma lem1163798 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term105 A B h f t) = ((term106 A B f h t) = (term107 A B h f t)).
Proof. exact (eq_refl (term105 A B h f t)). Qed.
Lemma lem1163800 {A B : Type'} : term95 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1163801 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (@lem1163800 A B f). Qed.
Lemma lem1163802 {A B : Type'} (f : A -> B) : (term96 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term96 A B f)). Qed.
Lemma lem1163804 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term108 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163805 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term109 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1163804 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163813 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1163802 A B f) (@lem1163801 A B f)). Qed.
Lemma lem1163814 {_27381 _27382 : Type'} (f : _27382 -> _27381) : (@List.map _27382 _27381 f (@nil _27382)) = (@nil _27381).
Proof. exact (@lem1163813 _27382 _27381 f). Qed.
Lemma lem1163815 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) : (@ALL2 _27381 _27380 P) = (@ALL2 _27381 _27380 P).
Proof. exact (eq_refl (@ALL2 _27381 _27380 P)). Qed.
Lemma lem1163816 {_27380 _27381 _27382 : Type'} (f : _27382 -> _27381) (P : type1470 _27380 _27381) : (term97 _27380 _27381 _27382 P f) = (@ALL2 _27381 _27380 P (@nil _27381)).
Proof. exact (MK_COMB (@lem1163815 _27380 _27381 P) (@lem1163814 _27381 _27382 f)). Qed.
Lemma lem1163818 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term106 A B f h t) = (term107 A B h f t).
Proof. exact (EQ_MP (@lem1163798 A B h f t) (@lem1163797 A B h f t)). Qed.
Lemma lem1163819 {_27380 _27383 : Type'} (h : _27383) (f : _27383 -> _27380) (t : list _27383) : (term110 _27380 _27383 f h t) = (term111 _27380 _27383 h f t).
Proof. exact (@lem1163818 _27383 _27380 h f t). Qed.
Lemma lem1163820 {_27380 _27383 : Type'} (h : _27383) (g : _27383 -> _27380) (t : list _27383) : (term110 _27380 _27383 g h t) = (term111 _27380 _27383 h g t).
Proof. exact (@lem1163819 _27380 _27383 h g t). Qed.
Lemma lem1163821 {_27380 _27381 _27382 _27383 : Type'} (f : _27382 -> _27381) (P : type1470 _27380 _27381) (h : _27383) (g : _27383 -> _27380) (t : list _27383) : (term44 _27380 _27381 _27382 _27383 P f g h t) = (term112 _27380 _27381 _27383 P h g t).
Proof. exact (MK_COMB (@lem1163816 _27380 _27381 _27382 f P) (@lem1163820 _27380 _27383 h g t)). Qed.
Lemma lem1163823 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term113 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1163805 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1163824 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) (h2' : _27380) (t2 : list _27380) : (term113 _27380 _27381 P h2' t2) = False.
Proof. exact (@lem1163823 _27380 _27381 P h2' t2). Qed.
Lemma lem1163825 {_27380 _27381 _27383 : Type'} (P : type1470 _27380 _27381) (h : _27383) (g : _27383 -> _27380) (t : list _27383) : (term112 _27380 _27381 _27383 P h g t) = False.
Proof. exact (@lem1163824 _27380 _27381 P (g h) (@List.map _27383 _27380 g t)). Qed.
Lemma lem1163826 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : (term44 _27380 _27381 _27382 _27383 P f g h t) = False.
Proof. exact (TRANS (@lem1163821 _27380 _27381 _27382 _27383 f P h g t) (@lem1163825 _27380 _27381 _27383 P h g t)). Qed.
Lemma lem1163827 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163828 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : (term114 _27380 _27381 _27382 _27383 P f g h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1163827) (@lem1163826 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163830 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term113 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1163805 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1163831 {_27382 _27383 : Type'} (P : type1413 _27382 _27383) (h2' : _27383) (t2 : list _27383) : (term115 _27382 _27383 P h2' t2) = False.
Proof. exact (@lem1163830 _27383 _27382 P h2' t2). Qed.
Lemma lem1163832 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : (term45 _27380 _27381 _27382 _27383 P f g h t) = False.
Proof. exact (@lem1163831 _27382 _27383 (term99 _27380 _27381 _27382 _27383 P f g) h t). Qed.
Lemma lem1163833 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : ((term44 _27380 _27381 _27382 _27383 P f g h t) = (term45 _27380 _27381 _27382 _27383 P f g h t)) = (False = False).
Proof. exact (MK_COMB (@lem1163828 _27380 _27381 _27382 _27383 P f g h t) (@lem1163832 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163835 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1163836 : (False = False) = (~ False).
Proof. exact (@lem1163835 False). Qed.
Lemma lem1163838 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1163839 : (False = False) = True.
Proof. exact (TRANS (@lem1163836) (@lem1163838)). Qed.
Lemma lem1163840 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : ((term44 _27380 _27381 _27382 _27383 P f g h t) = (term45 _27380 _27381 _27382 _27383 P f g h t)) = True.
Proof. exact (TRANS (@lem1163833 _27380 _27381 _27382 _27383 P f g h t) (@lem1163839)). Qed.
Lemma lem1163841 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : True = ((term44 _27380 _27381 _27382 _27383 P f g h t) = (term45 _27380 _27381 _27382 _27383 P f g h t)).
Proof. exact (SYM (@lem1163840 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163842 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : (term44 _27380 _27381 _27382 _27383 P f g h t) = (term45 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (EQ_MP (@lem1163841 _27380 _27381 _27382 _27383 P f g h t) (@lem0)). Qed.
Lemma lem1163843 {A B : Type'} : term100 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1163844 {A B : Type'} (f : A -> B) : term101 A B f.
Proof. exact (@lem1163843 A B f). Qed.
Lemma lem1163845 {A B : Type'} (f : A -> B) : (term101 A B f) = (term102 A B f).
Proof. exact (eq_refl (term101 A B f)). Qed.
Lemma lem1163846 {A B : Type'} (f : A -> B) : term102 A B f.
Proof. exact (EQ_MP (@lem1163845 A B f) (@lem1163844 A B f)). Qed.
Lemma lem1163847 {A B : Type'} (f : A -> B) (h : A) : term103 A B f h.
Proof. exact (@lem1163846 A B f h). Qed.
Lemma lem1163848 {A B : Type'} (h : A) (f : A -> B) : (term103 A B f h) = (term104 A B h f).
Proof. exact (eq_refl (term103 A B f h)). Qed.
Lemma lem1163849 {A B : Type'} (h : A) (f : A -> B) : term104 A B h f.
Proof. exact (EQ_MP (@lem1163848 A B h f) (@lem1163847 A B f h)). Qed.
Lemma lem1163850 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term105 A B h f t.
Proof. exact (@lem1163849 A B h f t). Qed.
Lemma lem1163851 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term105 A B h f t) = ((term106 A B f h t) = (term107 A B h f t)).
Proof. exact (eq_refl (term105 A B h f t)). Qed.
Lemma lem1163853 {A B : Type'} : term95 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem1163854 {A B : Type'} (f : A -> B) : term96 A B f.
Proof. exact (@lem1163853 A B f). Qed.
Lemma lem1163855 {A B : Type'} (f : A -> B) : (term96 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term96 A B f)). Qed.
Lemma lem1163857 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term108 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163869 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term106 A B f h t) = (term107 A B h f t).
Proof. exact (EQ_MP (@lem1163851 A B h f t) (@lem1163850 A B h f t)). Qed.
Lemma lem1163870 {_27381 _27382 : Type'} (h : _27382) (f : _27382 -> _27381) (t : list _27382) : (term110 _27381 _27382 f h t) = (term111 _27381 _27382 h f t).
Proof. exact (@lem1163869 _27382 _27381 h f t). Qed.
Lemma lem1163871 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) : (@ALL2 _27381 _27380 P) = (@ALL2 _27381 _27380 P).
Proof. exact (eq_refl (@ALL2 _27381 _27380 P)). Qed.
Lemma lem1163872 {_27380 _27381 _27382 : Type'} (P : type1470 _27380 _27381) (h : _27382) (f : _27382 -> _27381) (t : list _27382) : (term116 _27380 _27381 _27382 P f h t) = (term117 _27380 _27381 _27382 P h f t).
Proof. exact (MK_COMB (@lem1163871 _27380 _27381 P) (@lem1163870 _27381 _27382 h f t)). Qed.
Lemma lem1163874 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem1163855 A B f) (@lem1163854 A B f)). Qed.
Lemma lem1163875 {_27380 _27383 : Type'} (f : _27383 -> _27380) : (@List.map _27383 _27380 f (@nil _27383)) = (@nil _27380).
Proof. exact (@lem1163874 _27383 _27380 f). Qed.
Lemma lem1163876 {_27380 _27383 : Type'} (g : _27383 -> _27380) : (@List.map _27383 _27380 g (@nil _27383)) = (@nil _27380).
Proof. exact (@lem1163875 _27380 _27383 g). Qed.
Lemma lem1163877 {_27380 _27381 _27382 _27383 : Type'} (g : _27383 -> _27380) (P : type1470 _27380 _27381) (h : _27382) (f : _27382 -> _27381) (t : list _27382) : (term66 _27380 _27381 _27382 _27383 P f h t g) = (term118 _27380 _27381 _27382 P h f t).
Proof. exact (MK_COMB (@lem1163872 _27380 _27381 _27382 P h f t) (@lem1163876 _27380 _27383 g)). Qed.
Lemma lem1163879 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term119 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1163857 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1163880 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) (h1' : _27381) (t1 : list _27381) : (term119 _27380 _27381 P h1' t1) = False.
Proof. exact (@lem1163879 _27380 _27381 P h1' t1). Qed.
Lemma lem1163881 {_27380 _27381 _27382 : Type'} (P : type1470 _27380 _27381) (h : _27382) (f : _27382 -> _27381) (t : list _27382) : (term118 _27380 _27381 _27382 P h f t) = False.
Proof. exact (@lem1163880 _27380 _27381 P (f h) (@List.map _27382 _27381 f t)). Qed.
Lemma lem1163882 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (t : list _27382) (g : _27383 -> _27380) : (term66 _27380 _27381 _27382 _27383 P f h t g) = False.
Proof. exact (TRANS (@lem1163877 _27380 _27381 _27382 _27383 g P h f t) (@lem1163881 _27380 _27381 _27382 P h f t)). Qed.
Lemma lem1163883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163884 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (t : list _27382) (g : _27383 -> _27380) : (term120 _27380 _27381 _27382 _27383 P f h t g) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1163883) (@lem1163882 _27380 _27381 _27382 _27383 P f h t g)). Qed.
Lemma lem1163886 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term119 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1163857 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1163887 {_27382 _27383 : Type'} (P : type1413 _27382 _27383) (h1' : _27382) (t1 : list _27382) : (term121 _27382 _27383 P h1' t1) = False.
Proof. exact (@lem1163886 _27383 _27382 P h1' t1). Qed.
Lemma lem1163888 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term67 _27380 _27381 _27382 _27383 P f g h t) = False.
Proof. exact (@lem1163887 _27382 _27383 (term99 _27380 _27381 _27382 _27383 P f g) h t). Qed.
Lemma lem1163889 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : ((term66 _27380 _27381 _27382 _27383 P f h t g) = (term67 _27380 _27381 _27382 _27383 P f g h t)) = (False = False).
Proof. exact (MK_COMB (@lem1163884 _27380 _27381 _27382 _27383 P f h t g) (@lem1163888 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163891 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1163892 : (False = False) = (~ False).
Proof. exact (@lem1163891 False). Qed.
Lemma lem1163894 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1163895 : (False = False) = True.
Proof. exact (TRANS (@lem1163892) (@lem1163894)). Qed.
Lemma lem1163896 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : ((term66 _27380 _27381 _27382 _27383 P f h t g) = (term67 _27380 _27381 _27382 _27383 P f g h t)) = True.
Proof. exact (TRANS (@lem1163889 _27380 _27381 _27382 _27383 P f g h t) (@lem1163895)). Qed.
Lemma lem1163897 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : True = ((term66 _27380 _27381 _27382 _27383 P f h t g) = (term67 _27380 _27381 _27382 _27383 P f g h t)).
Proof. exact (SYM (@lem1163896 _27380 _27381 _27382 _27383 P f g h t)). Qed.
Lemma lem1163898 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : (term66 _27380 _27381 _27382 _27383 P f h t g) = (term67 _27380 _27381 _27382 _27383 P f g h t).
Proof. exact (EQ_MP (@lem1163897 _27380 _27381 _27382 _27383 P f g h t) (@lem0)). Qed.
Lemma lem1163899 {A B : Type'} : term100 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem1163900 {A B : Type'} (f : A -> B) : term101 A B f.
Proof. exact (@lem1163899 A B f). Qed.
Lemma lem1163901 {A B : Type'} (f : A -> B) : (term101 A B f) = (term102 A B f).
Proof. exact (eq_refl (term101 A B f)). Qed.
Lemma lem1163902 {A B : Type'} (f : A -> B) : term102 A B f.
Proof. exact (EQ_MP (@lem1163901 A B f) (@lem1163900 A B f)). Qed.
Lemma lem1163903 {A B : Type'} (f : A -> B) (h : A) : term103 A B f h.
Proof. exact (@lem1163902 A B f h). Qed.
Lemma lem1163904 {A B : Type'} (h : A) (f : A -> B) : (term103 A B f h) = (term104 A B h f).
Proof. exact (eq_refl (term103 A B f h)). Qed.
Lemma lem1163905 {A B : Type'} (h : A) (f : A -> B) : term104 A B h f.
Proof. exact (EQ_MP (@lem1163904 A B h f) (@lem1163903 A B f h)). Qed.
Lemma lem1163906 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term105 A B h f t.
Proof. exact (@lem1163905 A B h f t). Qed.
Lemma lem1163907 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term105 A B h f t) = ((term106 A B f h t) = (term107 A B h f t)).
Proof. exact (eq_refl (term105 A B h f t)). Qed.
Lemma lem1163913 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term108 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163914 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term109 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1163913 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163919 {_27380 _27381 _27382 _27383 : Type'} (m : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term122 _27380 _27381 _27382 _27383 P f g t m.
Proof. exact (@lem1163684 _27380 _27381 _27382 _27383 P f g t h1 m). Qed.
Lemma lem1163920 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (m : list _27383) : (term122 _27380 _27381 _27382 _27383 P f g t m) = ((term123 _27380 _27381 _27382 _27383 P f t g m) = (term124 _27380 _27381 _27382 _27383 P f g t m)).
Proof. exact (eq_refl (term122 _27380 _27381 _27382 _27383 P f g t m)). Qed.
Lemma lem1163925 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term106 A B f h t) = (term107 A B h f t).
Proof. exact (EQ_MP (@lem1163907 A B h f t) (@lem1163906 A B h f t)). Qed.
Lemma lem1163926 {_27381 _27382 : Type'} (h : _27382) (f : _27382 -> _27381) (t : list _27382) : (term110 _27381 _27382 f h t) = (term111 _27381 _27382 h f t).
Proof. exact (@lem1163925 _27382 _27381 h f t). Qed.
Lemma lem1163927 {_27380 _27381 : Type'} (P : type1470 _27380 _27381) : (@ALL2 _27381 _27380 P) = (@ALL2 _27381 _27380 P).
Proof. exact (eq_refl (@ALL2 _27381 _27380 P)). Qed.
Lemma lem1163928 {_27380 _27381 _27382 : Type'} (P : type1470 _27380 _27381) (h : _27382) (f : _27382 -> _27381) (t : list _27382) : (term116 _27380 _27381 _27382 P f h t) = (term117 _27380 _27381 _27382 P h f t).
Proof. exact (MK_COMB (@lem1163927 _27380 _27381 P) (@lem1163926 _27381 _27382 h f t)). Qed.
Lemma lem1163930 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term106 A B f h t) = (term107 A B h f t).
Proof. exact (EQ_MP (@lem1163907 A B h f t) (@lem1163906 A B h f t)). Qed.
Lemma lem1163931 {_27380 _27383 : Type'} (h : _27383) (f : _27383 -> _27380) (t : list _27383) : (term110 _27380 _27383 f h t) = (term111 _27380 _27383 h f t).
Proof. exact (@lem1163930 _27383 _27380 h f t). Qed.
Lemma lem1163932 {_27380 _27383 : Type'} (h' : _27383) (g : _27383 -> _27380) (t' : list _27383) : (term110 _27380 _27383 g h' t') = (term111 _27380 _27383 h' g t').
Proof. exact (@lem1163931 _27380 _27383 h' g t'). Qed.
Lemma lem1163933 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (h : _27382) (f : _27382 -> _27381) (t : list _27382) (h' : _27383) (g : _27383 -> _27380) (t' : list _27383) : (term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term125 _27380 _27381 _27382 _27383 P h f t h' g t').
Proof. exact (MK_COMB (@lem1163928 _27380 _27381 _27382 P h f t) (@lem1163932 _27380 _27383 h' g t')). Qed.
Lemma lem1163935 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term126 _25470 _25471 P h1' t1 h2' t2) = (term127 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1163914 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163936 {_27380 _27381 : Type'} (h1' : _27381) (h2' : _27380) (P : type1470 _27380 _27381) (t1 : list _27381) (t2 : list _27380) : (term126 _27380 _27381 P h1' t1 h2' t2) = (term127 _27380 _27381 h1' h2' P t1 t2).
Proof. exact (@lem1163935 _27380 _27381 h1' h2' P t1 t2). Qed.
Lemma lem1163937 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (t : list _27382) (g : _27383 -> _27380) (t' : list _27383) : (term125 _27380 _27381 _27382 _27383 P h f t h' g t') = (term128 _27380 _27381 _27382 _27383 h h' P f t g t').
Proof. exact (@lem1163936 _27380 _27381 (f h) (g h') P (@List.map _27382 _27381 f t) (@List.map _27383 _27380 g t')). Qed.
Lemma lem1163941 {_27380 _27381 _27382 _27383 : Type'} (m : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term123 _27380 _27381 _27382 _27383 P f t g m) = (term124 _27380 _27381 _27382 _27383 P f g t m).
Proof. exact (EQ_MP (@lem1163920 _27380 _27381 _27382 _27383 P f g t m) (@lem1163919 _27380 _27381 _27382 _27383 m P f g t h1)). Qed.
Lemma lem1163942 {_27380 _27381 _27382 _27383 : Type'} (m : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term123 _27380 _27381 _27382 _27383 P f t g m) = (term124 _27380 _27381 _27382 _27383 P f g t m).
Proof. exact (@lem1163941 _27380 _27381 _27382 _27383 m P f g t h1). Qed.
Lemma lem1163943 {_27380 _27381 _27382 _27383 : Type'} (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term123 _27380 _27381 _27382 _27383 P f t g t') = (term124 _27380 _27381 _27382 _27383 P f g t t').
Proof. exact (@lem1163942 _27380 _27381 _27382 _27383 t' P f g t h1). Qed.
Lemma lem1163944 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term129 _27380 _27381 _27382 _27383 P f h g h') = (term129 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (eq_refl (term129 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163945 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term128 _27380 _27381 _27382 _27383 h h' P f t g t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (MK_COMB (@lem1163944 _27380 _27381 _27382 _27383 P f h g h') (@lem1163943 _27380 _27381 _27382 _27383 t' P f g t h1)). Qed.
Lemma lem1163948 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term125 _27380 _27381 _27382 _27383 P h f t h' g t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (TRANS (@lem1163937 _27380 _27381 _27382 _27383 h h' P f t g t') (@lem1163945 _27380 _27381 _27382 _27383 h h' t' P f g t h1)). Qed.
Lemma lem1163949 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (TRANS (@lem1163933 _27380 _27381 _27382 _27383 P h f t h' g t') (@lem1163948 _27380 _27381 _27382 _27383 h h' t' P f g t h1)). Qed.
Lemma lem1163950 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163951 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term131 _27380 _27381 _27382 _27383 P f h t g h' t') = (term132 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (MK_COMB (@lem1163950) (@lem1163949 _27380 _27381 _27382 _27383 h h' t' P f g t h1)). Qed.
Lemma lem1163953 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term126 _25470 _25471 P h1' t1 h2' t2) = (term127 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1163914 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1163954 {_27382 _27383 : Type'} (h1' : _27382) (h2' : _27383) (P : type1413 _27382 _27383) (t1 : list _27382) (t2 : list _27383) : (term133 _27382 _27383 P h1' t1 h2' t2) = (term134 _27382 _27383 h1' h2' P t1 t2).
Proof. exact (@lem1163953 _27383 _27382 h1' h2' P t1 t2). Qed.
Lemma lem1163955 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (t' : list _27383) : (term77 _27380 _27381 _27382 _27383 P f g h t h' t') = (term135 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (@lem1163954 _27382 _27383 h h' (term99 _27380 _27381 _27382 _27383 P f g) t t'). Qed.
Lemma lem1163959 {A B : Type'} (f : A -> B) (y : A) : (term136 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1163960 {_27382 _27383 : Type'} (f : type1413 _27382 _27383) (y : _27382) : (term137 _27382 _27383 f y) = (f y).
Proof. exact (@lem1163959 _27382 (_27383 -> Prop) f y). Qed.
Lemma lem1163961 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) : (term138 _27380 _27381 _27382 _27383 P f g h) = (term139 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (@lem1163960 _27382 _27383 (term99 _27380 _27381 _27382 _27383 P f g) h). Qed.
Lemma lem1163962 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (x : _27382) (g : _27383 -> _27380) : (term139 _27380 _27381 _27382 _27383 P f g x) = (term140 _27380 _27381 _27382 _27383 P f x g).
Proof. exact (eq_refl (term139 _27380 _27381 _27382 _27383 P f g x)). Qed.
Lemma lem1163963 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : (term141 _27380 _27381 _27382 _27383 P f g) = (term99 _27380 _27381 _27382 _27383 P f g).
Proof. exact (fun_ext (fun x : _27382 => @lem1163962 _27380 _27381 _27382 _27383 P f x g)). Qed.
Lemma lem1163964 {_27382 : Type'} (h : _27382) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1163965 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) : (term138 _27380 _27381 _27382 _27383 P f g h) = (term139 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (MK_COMB (@lem1163963 _27380 _27381 _27382 _27383 P f g) (@lem1163964 _27382 h)). Qed.
Lemma lem1163966 {_27383 : Type'} : (@eq (_27383 -> Prop)) = (@eq (_27383 -> Prop)).
Proof. exact (eq_refl (@eq (_27383 -> Prop))). Qed.
Lemma lem1163967 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) : (term142 _27380 _27381 _27382 _27383 P f g h) = (term143 _27380 _27381 _27382 _27383 P f g h).
Proof. exact (MK_COMB (@lem1163966 _27383) (@lem1163965 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163968 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) : (term139 _27380 _27381 _27382 _27383 P f g h) = (term140 _27380 _27381 _27382 _27383 P f h g).
Proof. exact (eq_refl (term139 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163969 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) : ((term138 _27380 _27381 _27382 _27383 P f g h) = (term139 _27380 _27381 _27382 _27383 P f g h)) = ((term139 _27380 _27381 _27382 _27383 P f g h) = (term140 _27380 _27381 _27382 _27383 P f h g)).
Proof. exact (MK_COMB (@lem1163967 _27380 _27381 _27382 _27383 P f g h) (@lem1163968 _27380 _27381 _27382 _27383 P f h g)). Qed.
Lemma lem1163970 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) : (term139 _27380 _27381 _27382 _27383 P f g h) = (term140 _27380 _27381 _27382 _27383 P f h g).
Proof. exact (EQ_MP (@lem1163969 _27380 _27381 _27382 _27383 P f h g) (@lem1163961 _27380 _27381 _27382 _27383 P f g h)). Qed.
Lemma lem1163971 {_27383 : Type'} (h' : _27383) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1163972 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term144 _27380 _27381 _27382 _27383 P f g h h') = (term145 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (MK_COMB (@lem1163970 _27380 _27381 _27382 _27383 P f h g) (@lem1163971 _27383 h')). Qed.
Lemma lem1163974 {A B : Type'} (f : A -> B) (y : A) : (term136 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1163975 {_27383 : Type'} (f : _27383 -> Prop) (y : _27383) : (term146 _27383 f y) = (f y).
Proof. exact (@lem1163974 _27383 Prop f y). Qed.
Lemma lem1163976 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term147 _27380 _27381 _27382 _27383 P f h g h') = (term145 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (@lem1163975 _27383 (term140 _27380 _27381 _27382 _27383 P f h g) h'). Qed.
Lemma lem1163977 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (y : _27383) : (term145 _27380 _27381 _27382 _27383 P f h g y) = (term148 _27380 _27381 _27382 _27383 P f h g y).
Proof. exact (eq_refl (term145 _27380 _27381 _27382 _27383 P f h g y)). Qed.
Lemma lem1163978 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) : (term149 _27380 _27381 _27382 _27383 P f h g) = (term140 _27380 _27381 _27382 _27383 P f h g).
Proof. exact (fun_ext (fun y : _27383 => @lem1163977 _27380 _27381 _27382 _27383 P f h g y)). Qed.
Lemma lem1163979 {_27383 : Type'} (h' : _27383) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1163980 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term147 _27380 _27381 _27382 _27383 P f h g h') = (term145 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (MK_COMB (@lem1163978 _27380 _27381 _27382 _27383 P f h g) (@lem1163979 _27383 h')). Qed.
Lemma lem1163981 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1163982 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term150 _27380 _27381 _27382 _27383 P f h g h') = (term151 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (MK_COMB (@lem1163981) (@lem1163980 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163983 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term145 _27380 _27381 _27382 _27383 P f h g h') = (term148 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (eq_refl (term145 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163984 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : ((term147 _27380 _27381 _27382 _27383 P f h g h') = (term145 _27380 _27381 _27382 _27383 P f h g h')) = ((term145 _27380 _27381 _27382 _27383 P f h g h') = (term148 _27380 _27381 _27382 _27383 P f h g h')).
Proof. exact (MK_COMB (@lem1163982 _27380 _27381 _27382 _27383 P f h g h') (@lem1163983 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163985 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term145 _27380 _27381 _27382 _27383 P f h g h') = (term148 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (EQ_MP (@lem1163984 _27380 _27381 _27382 _27383 P f h g h') (@lem1163976 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163986 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term144 _27380 _27381 _27382 _27383 P f g h h') = (term148 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (TRANS (@lem1163972 _27380 _27381 _27382 _27383 P f h g h') (@lem1163985 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163987 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1163988 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (h : _27382) (g : _27383 -> _27380) (h' : _27383) : (term152 _27380 _27381 _27382 _27383 P f g h h') = (term129 _27380 _27381 _27382 _27383 P f h g h').
Proof. exact (MK_COMB (@lem1163987) (@lem1163986 _27380 _27381 _27382 _27383 P f h g h')). Qed.
Lemma lem1163989 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (t' : list _27383) : (term124 _27380 _27381 _27382 _27383 P f g t t') = (term124 _27380 _27381 _27382 _27383 P f g t t').
Proof. exact (eq_refl (term124 _27380 _27381 _27382 _27383 P f g t t')). Qed.
Lemma lem1163990 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (t' : list _27383) : (term135 _27380 _27381 _27382 _27383 h h' P f g t t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (MK_COMB (@lem1163988 _27380 _27381 _27382 _27383 P f h g h') (@lem1163989 _27380 _27381 _27382 _27383 P f g t t')). Qed.
Lemma lem1163993 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (t' : list _27383) : (term77 _27380 _27381 _27382 _27383 P f g h t h' t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t').
Proof. exact (TRANS (@lem1163955 _27380 _27381 _27382 _27383 h h' P f g t t') (@lem1163990 _27380 _27381 _27382 _27383 h h' P f g t t')). Qed.
Lemma lem1163994 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : ((term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term77 _27380 _27381 _27382 _27383 P f g h t h' t')) = ((term130 _27380 _27381 _27382 _27383 h h' P f g t t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t')).
Proof. exact (MK_COMB (@lem1163951 _27380 _27381 _27382 _27383 h h' t' P f g t h1) (@lem1163993 _27380 _27381 _27382 _27383 h h' P f g t t')). Qed.
Lemma lem1163996 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1163997 (x : Prop) : (x = x) = True.
Proof. exact (@lem1163996 Prop x). Qed.
Lemma lem1163998 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (t' : list _27383) : ((term130 _27380 _27381 _27382 _27383 h h' P f g t t') = (term130 _27380 _27381 _27382 _27383 h h' P f g t t')) = True.
Proof. exact (@lem1163997 (term130 _27380 _27381 _27382 _27383 h h' P f g t t')). Qed.
Lemma lem1163999 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : ((term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term77 _27380 _27381 _27382 _27383 P f g h t h' t')) = True.
Proof. exact (TRANS (@lem1163994 _27380 _27381 _27382 _27383 h h' t' P f g t h1) (@lem1163998 _27380 _27381 _27382 _27383 h h' P f g t t')). Qed.
Lemma lem1164000 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : True = ((term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term77 _27380 _27381 _27382 _27383 P f g h t h' t')).
Proof. exact (SYM (@lem1163999 _27380 _27381 _27382 _27383 h h' t' P f g t h1)). Qed.
Lemma lem1164001 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : (term76 _27380 _27381 _27382 _27383 P f h t g h' t') = (term77 _27380 _27381 _27382 _27383 P f g h t h' t').
Proof. exact (EQ_MP (@lem1164000 _27380 _27381 _27382 _27383 h h' t' P f g t h1) (@lem0)). Qed.
Lemma lem1164002 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (t' : list _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term79 _27380 _27381 _27382 _27383 P f g h t h' t'.
Proof. exact (fun h0 : (term71 _27380 _27381 _27382 _27383 P f h t g t') = (term72 _27380 _27381 _27382 _27383 P f g h t t') => @lem1164001 _27380 _27381 _27382 _27383 h h' t' P f g t h1). Qed.
Lemma lem1164007 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (h' : _27383) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term83 _27380 _27381 _27382 _27383 P f g h t h'.
Proof. exact (fun t' : list _27383 => @lem1164002 _27380 _27381 _27382 _27383 h h' t' P f g t h1). Qed.
Lemma lem1164012 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term87 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (fun h' : _27383 => @lem1164007 _27380 _27381 _27382 _27383 h h' P f g t h1). Qed.
Lemma lem1164013 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term89 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (conj (@lem1163898 _27380 _27381 _27382 _27383 P f g h t) (@lem1164012 _27380 _27381 _27382 _27383 h P f g t h1)). Qed.
Lemma lem1164014 {_27380 _27381 _27382 _27383 : Type'} (h : _27382) (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (t : list _27382) (h1 : term8 _27380 _27381 _27382 _27383 P f g t) : term12 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (@lem1163739 _27380 _27381 _27382 _27383 P f g h t (@lem1164013 _27380 _27381 _27382 _27383 h P f g t h1)). Qed.
Lemma lem1164015 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) (t : list _27383) : term47 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (fun h0 : (term39 _27380 _27381 _27382 _27383 P f g t) = (term40 _27380 _27381 _27382 _27383 P f g t) => @lem1163842 _27380 _27381 _27382 _27383 P f g h t). Qed.
Lemma lem1164020 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27383) : term51 _27380 _27381 _27382 _27383 P f g h.
Proof. exact (fun t : list _27383 => @lem1164015 _27380 _27381 _27382 _27383 P f g h t). Qed.
Lemma lem1164025 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term55 _27380 _27381 _27382 _27383 P f g.
Proof. exact (fun h : _27383 => @lem1164020 _27380 _27381 _27382 _27383 P f g h). Qed.
Lemma lem1164026 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term57 _27380 _27381 _27382 _27383 P f g.
Proof. exact (conj (@lem1163789 _27380 _27381 _27382 _27383 P f g) (@lem1164025 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1164027 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term4 _27380 _27381 _27382 _27383 P f g.
Proof. exact (@lem1163711 _27380 _27381 _27382 _27383 P f g (@lem1164026 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1164028 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) (t : list _27382) : term14 _27380 _27381 _27382 _27383 P f g h t.
Proof. exact (fun h0 : term8 _27380 _27381 _27382 _27383 P f g t => @lem1164014 _27380 _27381 _27382 _27383 h P f g t h0). Qed.
Lemma lem1164033 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) (h : _27382) : term18 _27380 _27381 _27382 _27383 P f g h.
Proof. exact (fun t : list _27382 => @lem1164028 _27380 _27381 _27382 _27383 P f g h t). Qed.
Lemma lem1164038 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term22 _27380 _27381 _27382 _27383 P f g.
Proof. exact (fun h : _27382 => @lem1164033 _27380 _27381 _27382 _27383 P f g h). Qed.
Lemma lem1164039 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term24 _27380 _27381 _27382 _27383 P f g.
Proof. exact (conj (@lem1164027 _27380 _27381 _27382 _27383 P f g) (@lem1164038 _27380 _27381 _27382 _27383 P f g)). Qed.
Lemma lem1164040 {_27380 _27381 _27382 _27383 : Type'} (P : type1470 _27380 _27381) (f : _27382 -> _27381) (g : _27383 -> _27380) : term29 _27380 _27381 _27382 _27383 P f g.
Proof. exact (@lem1163683 _27380 _27381 _27382 _27383 P f g (@lem1164039 _27380 _27381 _27382 _27383 P f g)). Qed.
