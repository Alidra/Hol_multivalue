Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ITERATE_CLOSED_term_abbrevs.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import IN_INSERT_spec.
Require Import IN_SUPPORT_spec.
Require Import ITERATE_CLAUSES_spec.
Require Import ITERATE_EXPAND_CASES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm196_spec.
Require Import thm197_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem5778670 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5778671 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem5778670 A h1 P). Qed.
Lemma lem5778672 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem5778673 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem5778672 A P) (@lem5778671 A P h1)). Qed.
Lemma lem5778674 {A : Type'} (P : type686 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem5778675 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem5778673 A P h1 (@lem5778674 A P h2)). Qed.
Lemma lem5778676 {A : Type'} (P : type686 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term0 A => @lem5778675 A P h0 h1). Qed.
Lemma lem5778677 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem5778678 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem5778676 A P h2 (@lem5778677 A h1)). Qed.
Lemma lem5778679 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun h0 : term3 A P => @lem5778678 A P h1 h0). Qed.
Lemma lem5778680 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem5778679 A P h1). Qed.
Lemma lem5778681 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem5778680 A h0). Qed.
Lemma lem5778682 {A : Type'} : term0 A.
Proof. exact (@lem5778681 A (@lem3558722 A)). Qed.
Lemma lem5778683 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem5778682 A P). Qed.
Lemma lem5778684 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem5778690 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) (h1 : (term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op)) : (term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op).
Proof. exact (h1). Qed.
Lemma lem5778691 {_119826 _119829 : Type'} (s : _119829 -> Prop) (f : _119829 -> _119826) (x : _119829) (op : type1400 _119826) (h1 : (term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op)) : (term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s).
Proof. exact (SYM (@lem5778690 _119826 _119829 s f x op h1)). Qed.
Lemma lem5778692 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) (s : _119829 -> Prop) (h1 : (term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s)) : (term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s).
Proof. exact (h1). Qed.
Lemma lem5778693 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) (s : _119829 -> Prop) (h1 : (term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s)) : (term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op).
Proof. exact (SYM (@lem5778692 _119826 _119829 x op f s h1)). Qed.
Lemma lem5778694 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) (s : _119829 -> Prop) : ((term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op)) = ((term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s)).
Proof. exact (prop_ext (fun h1 : (term7 _119826 _119829 x op f s) = (term8 _119826 _119829 s f x op) => @lem5778691 _119826 _119829 s f x op h1) (fun h1 : (term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s) => @lem5778693 _119826 _119829 x op f s h1)). Qed.
Lemma lem5778695 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) : (term9 _119826 _119829 f x op) = (term10 _119826 _119829 x op f).
Proof. exact (fun_ext (fun s : _119829 -> Prop => @lem5778694 _119826 _119829 x op f s)). Qed.
Lemma lem5778696 {_119829 : Type'} : (@all (_119829 -> Prop)) = (@all (_119829 -> Prop)).
Proof. exact (eq_refl (@all (_119829 -> Prop))). Qed.
Lemma lem5778697 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) : (term11 _119826 _119829 f x op) = (term12 _119826 _119829 x op f).
Proof. exact (MK_COMB (@lem5778696 _119829) (@lem5778695 _119826 _119829 x op f)). Qed.
Lemma lem5778698 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : (term13 _119826 _119829 f op) = (term14 _119826 _119829 op f).
Proof. exact (fun_ext (fun x : _119829 => @lem5778697 _119826 _119829 x op f)). Qed.
Lemma lem5778699 {_119829 : Type'} : (@all _119829) = (@all _119829).
Proof. exact (eq_refl (@all _119829)). Qed.
Lemma lem5778700 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : (term15 _119826 _119829 f op) = (term16 _119826 _119829 op f).
Proof. exact (MK_COMB (@lem5778699 _119829) (@lem5778698 _119826 _119829 op f)). Qed.
Lemma lem5778701 {_119826 _119829 : Type'} (op : type1400 _119826) : (term17 _119826 _119829 op) = (term18 _119826 _119829 op).
Proof. exact (fun_ext (fun f : _119829 -> _119826 => @lem5778700 _119826 _119829 op f)). Qed.
Lemma lem5778702 {_119826 _119829 : Type'} : (@all (_119829 -> _119826)) = (@all (_119829 -> _119826)).
Proof. exact (eq_refl (@all (_119829 -> _119826))). Qed.
Lemma lem5778703 {_119826 _119829 : Type'} (op : type1400 _119826) : (term19 _119826 _119829 op) = (term20 _119826 _119829 op).
Proof. exact (MK_COMB (@lem5778702 _119826 _119829) (@lem5778701 _119826 _119829 op)). Qed.
Lemma lem5778704 {_119826 _119829 : Type'} : (term21 _119826 _119829) = (term22 _119826 _119829).
Proof. exact (fun_ext (fun op : type1400 _119826 => @lem5778703 _119826 _119829 op)). Qed.
Lemma lem5778705 {_119826 : Type'} : (@all (_119826 -> _119826 -> _119826)) = (@all (_119826 -> _119826 -> _119826)).
Proof. exact (eq_refl (@all (_119826 -> _119826 -> _119826))). Qed.
Lemma lem5778706 {_119826 _119829 : Type'} : (term23 _119826 _119829) = (term24 _119826 _119829).
Proof. exact (MK_COMB (@lem5778705 _119826) (@lem5778704 _119826 _119829)). Qed.
Lemma lem5778707 {_119826 _119829 : Type'} : term24 _119826 _119829.
Proof. exact (EQ_MP (@lem5778706 _119826 _119829) (@lem5718201 _119826 _119829)). Qed.
Lemma lem5778708 {_119826 _119829 : Type'} (op : type1400 _119826) : term25 _119826 _119829 op.
Proof. exact (@lem5778707 _119826 _119829 op). Qed.
Lemma lem5778709 {_119826 _119829 : Type'} (op : type1400 _119826) : (term25 _119826 _119829 op) = (term20 _119826 _119829 op).
Proof. exact (eq_refl (term25 _119826 _119829 op)). Qed.
Lemma lem5778710 {_119826 _119829 : Type'} (op : type1400 _119826) : term20 _119826 _119829 op.
Proof. exact (EQ_MP (@lem5778709 _119826 _119829 op) (@lem5778708 _119826 _119829 op)). Qed.
Lemma lem5778711 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : term26 _119826 _119829 op f.
Proof. exact (@lem5778710 _119826 _119829 op f). Qed.
Lemma lem5778712 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : (term26 _119826 _119829 op f) = (term16 _119826 _119829 op f).
Proof. exact (eq_refl (term26 _119826 _119829 op f)). Qed.
Lemma lem5778713 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) : term16 _119826 _119829 op f.
Proof. exact (EQ_MP (@lem5778712 _119826 _119829 op f) (@lem5778711 _119826 _119829 op f)). Qed.
Lemma lem5778714 {_119826 _119829 : Type'} (op : type1400 _119826) (f : _119829 -> _119826) (x : _119829) : term27 _119826 _119829 op f x.
Proof. exact (@lem5778713 _119826 _119829 op f x). Qed.
Lemma lem5778715 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) : (term27 _119826 _119829 op f x) = (term12 _119826 _119829 x op f).
Proof. exact (eq_refl (term27 _119826 _119829 op f x)). Qed.
Lemma lem5778716 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) : term12 _119826 _119829 x op f.
Proof. exact (EQ_MP (@lem5778715 _119826 _119829 x op f) (@lem5778714 _119826 _119829 op f x)). Qed.
Lemma lem5778717 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) (s : _119829 -> Prop) : term28 _119826 _119829 x op f s.
Proof. exact (@lem5778716 _119826 _119829 x op f s). Qed.
Lemma lem5778718 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) (s : _119829 -> Prop) : (term28 _119826 _119829 x op f s) = ((term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s)).
Proof. exact (eq_refl (term28 _119826 _119829 x op f s)). Qed.
Lemma lem5778720 {_120327 _120333 : Type'} (op : type1400 _120327) : term29 _120327 _120333 op.
Proof. exact (@lem5738118 _120327 _120333 op). Qed.
Lemma lem5778721 {_120327 _120333 : Type'} (op : type1400 _120327) : (term29 _120327 _120333 op) = (term30 _120327 _120333 op).
Proof. exact (eq_refl (term29 _120327 _120333 op)). Qed.
Lemma lem5778722 {_120327 _120333 : Type'} (op : type1400 _120327) : term30 _120327 _120333 op.
Proof. exact (EQ_MP (@lem5778721 _120327 _120333 op) (@lem5778720 _120327 _120333 op)). Qed.
Lemma lem5778723 {_120327 _120333 : Type'} (op : type1400 _120327) (f : _120333 -> _120327) : term31 _120327 _120333 op f.
Proof. exact (@lem5778722 _120327 _120333 op f). Qed.
Lemma lem5778724 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : (term31 _120327 _120333 op f) = (term32 _120327 _120333 f op).
Proof. exact (eq_refl (term31 _120327 _120333 op f)). Qed.
Lemma lem5778725 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) : term32 _120327 _120333 f op.
Proof. exact (EQ_MP (@lem5778724 _120327 _120333 f op) (@lem5778723 _120327 _120333 op f)). Qed.
Lemma lem5778726 {_120327 _120333 : Type'} (f : _120333 -> _120327) (op : type1400 _120327) (s : _120333 -> Prop) : term33 _120327 _120333 f op s.
Proof. exact (@lem5778725 _120327 _120333 f op s). Qed.
Lemma lem5778727 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (term33 _120327 _120333 f op s) = ((@iterate _120327 _120333 op s f) = (term34 _120327 _120333 s f op)).
Proof. exact (eq_refl (term33 _120327 _120333 f op s)). Qed.
Lemma lem5778729 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5778730 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term35 B P op) : term35 B P op.
Proof. exact (h1). Qed.
Lemma lem5778731 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term36 B P op.
Proof. exact (h1). Qed.
Lemma lem5778732 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term37 B P op.
Proof. exact (h1). Qed.
Lemma lem5778733 {A B : Type'} (s : A -> Prop) (op : type1400 B) (P : B -> Prop) (f : A -> B) (h1 : term38 A B s op P f) : term38 A B s op P f.
Proof. exact (h1). Qed.
Lemma lem5778735 {_120327 _120333 : Type'} (s : _120333 -> Prop) (f : _120333 -> _120327) (op : type1400 _120327) : (@iterate _120327 _120333 op s f) = (term34 _120327 _120333 s f op).
Proof. exact (EQ_MP (@lem5778727 _120327 _120333 s f op) (@lem5778726 _120327 _120333 f op s)). Qed.
Lemma lem5778736 {A B : Type'} (s : A -> Prop) (f : A -> B) (op : type1400 B) : (@iterate B A op s f) = (term39 A B s f op).
Proof. exact (@lem5778735 B A s f op). Qed.
Lemma lem5778737 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem5778738 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term40 A B P op s f) = (term41 A B P s f op).
Proof. exact (MK_COMB (@lem5778737 B P) (@lem5778736 A B s f op)). Qed.
Lemma lem5778739 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term41 A B P s f op) = (term40 A B P op s f).
Proof. exact (SYM (@lem5778738 A B P s f op)). Qed.
Lemma lem5778767 {_119826 _119829 : Type'} (x : _119829) (op : type1400 _119826) (f : _119829 -> _119826) (s : _119829 -> Prop) : (term8 _119826 _119829 s f x op) = (term7 _119826 _119829 x op f s).
Proof. exact (EQ_MP (@lem5778718 _119826 _119829 x op f s) (@lem5778717 _119826 _119829 x op f s)). Qed.
Lemma lem5778768 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term42 A B s f x op) = (term43 A B x op f s).
Proof. exact (@lem5778767 B A x op f s). Qed.
Lemma lem5778769 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5778770 {A B : Type'} (x : A) (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term44 A B s f x op) = (term45 A B x op f s).
Proof. exact (MK_COMB (@lem5778769) (@lem5778768 A B x op f s)). Qed.
Lemma lem5778771 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) : (term46 A B P f x) = (term46 A B P f x).
Proof. exact (eq_refl (term46 A B P f x)). Qed.
Lemma lem5778772 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x : A) : (term47 A B s op P f x) = (term48 A B op s P f x).
Proof. exact (MK_COMB (@lem5778770 A B x op f s) (@lem5778771 A B P f x)). Qed.
Lemma lem5778775 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term49 A B s op P f) = (term50 A B op s P f).
Proof. exact (fun_ext (fun x : A => @lem5778772 A B op s P f x)). Qed.
Lemma lem5778776 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5778777 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term38 A B s op P f) = (term51 A B op s P f).
Proof. exact (MK_COMB (@lem5778776 A) (@lem5778775 A B op s P f)). Qed.
Lemma lem5778782 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5778783 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term52 A B s op P f) = (term53 A B op s P f).
Proof. exact (MK_COMB (@lem5778782) (@lem5778777 A B op s P f)). Qed.
Lemma lem5778784 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term41 A B P s f op) = (term41 A B P s f op).
Proof. exact (eq_refl (term41 A B P s f op)). Qed.
Lemma lem5778785 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term54 A B P s f op) = (term55 A B P s f op).
Proof. exact (MK_COMB (@lem5778783 A B op s P f) (@lem5778784 A B P s f op)). Qed.
Lemma lem5778788 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term56 B P op) = (term56 B P op).
Proof. exact (eq_refl (term56 B P op)). Qed.
Lemma lem5778789 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term57 A B P s f op) = (term58 A B P s f op).
Proof. exact (MK_COMB (@lem5778788 B P op) (@lem5778785 A B P s f op)). Qed.
Lemma lem5778792 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term59 B P op) = (term59 B P op).
Proof. exact (eq_refl (term59 B P op)). Qed.
Lemma lem5778793 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term60 A B P s f op) = (term61 A B P s f op).
Proof. exact (MK_COMB (@lem5778792 B P op) (@lem5778789 A B P s f op)). Qed.
Lemma lem5778796 {B : Type'} (op : type1400 B) : (term62 B op) = (term62 B op).
Proof. exact (eq_refl (term62 B op)). Qed.
Lemma lem5778797 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term63 A B P s f op) = (term64 A B P s f op).
Proof. exact (MK_COMB (@lem5778796 B op) (@lem5778793 A B P s f op)). Qed.
Lemma lem5778800 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term64 A B P s f op) = (term63 A B P s f op).
Proof. exact (SYM (@lem5778797 A B P s f op)). Qed.
Lemma lem5778801 {B : Type'} (_474 : B) (_475 : Prop) (_476 : B -> Prop) (_477 : B) : (term65 B _476 _475 _474 _477) = (term66 B _474 _475 _476 _477).
Proof. exact (@lem13473 B _474 _475 _476 _477). Qed.
Lemma lem5778802 {A B : Type'} (_474 : B) (_475 : Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (_477 : B) : (term67 A B op s f P _475 _474 _477) = (term68 A B _474 _475 op s f P _477).
Proof. exact (@lem5778801 B _474 _475 (term69 A B op s f P) _477). Qed.
Lemma lem5778803 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term70 A B P s f op) = (term71 A B s f P op).
Proof. exact (@lem5778802 A B (term72 A B op s f) (term73 A B op f s) op s f P (@neutral B op)). Qed.
Lemma lem5778804 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term74 A B s f P op) = (term75 A B s f P op).
Proof. exact (eq_refl (term74 A B s f P op)). Qed.
Lemma lem5778805 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term76 A B op f s) = (term76 A B op f s).
Proof. exact (eq_refl (term76 A B op f s)). Qed.
Lemma lem5778806 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term77 A B s f P op) = (term78 A B s f P op).
Proof. exact (MK_COMB (@lem5778805 A B op f s) (@lem5778804 A B s f P op)). Qed.
Lemma lem5778807 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term79 A B P op s f) = (term80 A B P op s f).
Proof. exact (eq_refl (term79 A B P op s f)). Qed.
Lemma lem5778808 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) : (term81 A B op f s) = (term81 A B op f s).
Proof. exact (eq_refl (term81 A B op f s)). Qed.
Lemma lem5778809 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term82 A B P op s f) = (term83 A B P op s f).
Proof. exact (MK_COMB (@lem5778808 A B op f s) (@lem5778807 A B P op s f)). Qed.
Lemma lem5778810 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5778811 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term84 A B P op s f) = (term85 A B P op s f).
Proof. exact (MK_COMB (@lem5778810) (@lem5778809 A B P op s f)). Qed.
Lemma lem5778812 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term71 A B s f P op) = (term86 A B s f P op).
Proof. exact (MK_COMB (@lem5778811 A B P op s f) (@lem5778806 A B s f P op)). Qed.
Lemma lem5778813 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term70 A B P s f op) = (term64 A B P s f op).
Proof. exact (eq_refl (term70 A B P s f op)). Qed.
Lemma lem5778814 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5778815 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term87 A B P s f op) = (term88 A B P s f op).
Proof. exact (MK_COMB (@lem5778814) (@lem5778813 A B P s f op)). Qed.
Lemma lem5778816 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : ((term70 A B P s f op) = (term71 A B s f P op)) = ((term64 A B P s f op) = (term86 A B s f P op)).
Proof. exact (MK_COMB (@lem5778815 A B P s f op) (@lem5778812 A B s f P op)). Qed.
Lemma lem5778817 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term64 A B P s f op) = (term86 A B s f P op).
Proof. exact (EQ_MP (@lem5778816 A B s f P op) (@lem5778803 A B s f P op)). Qed.
Lemma lem5778818 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : (term86 A B s f P op) = (term64 A B P s f op).
Proof. exact (SYM (@lem5778817 A B s f P op)). Qed.
Lemma lem5778819 {A B : Type'} (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term73 A B op f s) : term73 A B op f s.
Proof. exact (h1). Qed.
Lemma lem5780083 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780084 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780083 p q p' q'). Qed.
Lemma lem5780085 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780084 p q p'). Qed.
Lemma lem5780086 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term92 A B s f P op.
Proof. exact (@lem5780085 (@monoidal B op) (term93 A B s f P op)). Qed.
Lemma lem5780087 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term94 A B s f P op p'.
Proof. exact (@lem5780086 A B s f P op p'). Qed.
Lemma lem5780088 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : (term94 A B s f P op p') = (term95 A B s f P op p').
Proof. exact (eq_refl (term94 A B s f P op p')). Qed.
Lemma lem5780089 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term95 A B s f P op p'.
Proof. exact (EQ_MP (@lem5780088 A B s f P op p') (@lem5780087 A B s f P op p')). Qed.
Lemma lem5780090 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term96 A B s f P op p' q'.
Proof. exact (@lem5780089 A B s f P op p' q'). Qed.
Lemma lem5780091 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : (term96 A B s f P op p' q') = (term97 A B s f P op p' q').
Proof. exact (eq_refl (term96 A B s f P op p' q')). Qed.
Lemma lem5780092 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term97 A B s f P op p' q'.
Proof. exact (EQ_MP (@lem5780091 A B s f P op p' q') (@lem5780090 A B s f P op p' q')). Qed.
Lemma lem5780093 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@monoidal B op).
Proof. exact (eq_refl (@monoidal B op)). Qed.
Lemma lem5780094 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term98 A B s f P op q'.
Proof. exact (@lem5780092 A B s f P op (@monoidal B op) q'). Qed.
Lemma lem5780095 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term99 A B s f P op q'.
Proof. exact (@lem5780094 A B s f P op q' (@lem5780093 B op)). Qed.
Lemma lem5780102 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780103 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780102 p q p' q'). Qed.
Lemma lem5780104 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780103 p q p'). Qed.
Lemma lem5780105 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term100 A B s f P op.
Proof. exact (@lem5780104 (term37 B P op) (term101 A B s f P op)). Qed.
Lemma lem5780106 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term102 A B s f P op p'.
Proof. exact (@lem5780105 A B s f P op p'). Qed.
Lemma lem5780107 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : (term102 A B s f P op p') = (term103 A B s f P op p').
Proof. exact (eq_refl (term102 A B s f P op p')). Qed.
Lemma lem5780108 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term103 A B s f P op p'.
Proof. exact (EQ_MP (@lem5780107 A B s f P op p') (@lem5780106 A B s f P op p')). Qed.
Lemma lem5780109 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term104 A B s f P op p' q'.
Proof. exact (@lem5780108 A B s f P op p' q'). Qed.
Lemma lem5780110 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : (term104 A B s f P op p' q') = (term105 A B s f P op p' q').
Proof. exact (eq_refl (term104 A B s f P op p' q')). Qed.
Lemma lem5780111 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term105 A B s f P op p' q'.
Proof. exact (EQ_MP (@lem5780110 A B s f P op p' q') (@lem5780109 A B s f P op p' q')). Qed.
Lemma lem5780112 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term37 B P op) = (term37 B P op).
Proof. exact (eq_refl (term37 B P op)). Qed.
Lemma lem5780113 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term106 A B s f P op q'.
Proof. exact (@lem5780111 A B s f P op (term37 B P op) q'). Qed.
Lemma lem5780114 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term107 A B s f P op q'.
Proof. exact (@lem5780113 A B s f P op q' (@lem5780112 B P op)). Qed.
Lemma lem5780115 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term37 B P op.
Proof. exact (h1). Qed.
Lemma lem5780116 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term37 B P op) = ((term37 B P op) = True).
Proof. exact (@lem7 (term37 B P op)). Qed.
Lemma lem5780121 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780122 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780121 p q p' q'). Qed.
Lemma lem5780123 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780122 p q p'). Qed.
Lemma lem5780124 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term108 A B s f P op.
Proof. exact (@lem5780123 (term36 B P op) (term109 A B s f P op)). Qed.
Lemma lem5780125 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term110 A B s f P op p'.
Proof. exact (@lem5780124 A B s f P op p'). Qed.
Lemma lem5780126 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : (term110 A B s f P op p') = (term111 A B s f P op p').
Proof. exact (eq_refl (term110 A B s f P op p')). Qed.
Lemma lem5780127 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term111 A B s f P op p'.
Proof. exact (EQ_MP (@lem5780126 A B s f P op p') (@lem5780125 A B s f P op p')). Qed.
Lemma lem5780128 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term112 A B s f P op p' q'.
Proof. exact (@lem5780127 A B s f P op p' q'). Qed.
Lemma lem5780129 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : (term112 A B s f P op p' q') = (term113 A B s f P op p' q').
Proof. exact (eq_refl (term112 A B s f P op p' q')). Qed.
Lemma lem5780130 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term113 A B s f P op p' q'.
Proof. exact (EQ_MP (@lem5780129 A B s f P op p' q') (@lem5780128 A B s f P op p' q')). Qed.
Lemma lem5780170 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term36 B P op) = (term36 B P op).
Proof. exact (eq_refl (term36 B P op)). Qed.
Lemma lem5780171 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term114 A B s f P op q'.
Proof. exact (@lem5780130 A B s f P op (term36 B P op) q'). Qed.
Lemma lem5780172 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term115 A B s f P op q'.
Proof. exact (@lem5780171 A B s f P op q' (@lem5780170 B P op)). Qed.
Lemma lem5780192 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780193 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780192 p q p' q'). Qed.
Lemma lem5780194 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780193 p q p'). Qed.
Lemma lem5780195 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term116 A B s f P op.
Proof. exact (@lem5780194 (term51 A B op s P f) (term37 B P op)). Qed.
Lemma lem5780196 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term117 A B s f P op p'.
Proof. exact (@lem5780195 A B s f P op p'). Qed.
Lemma lem5780197 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : (term117 A B s f P op p') = (term118 A B s f P op p').
Proof. exact (eq_refl (term117 A B s f P op p')). Qed.
Lemma lem5780198 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) : term118 A B s f P op p'.
Proof. exact (EQ_MP (@lem5780197 A B s f P op p') (@lem5780196 A B s f P op p')). Qed.
Lemma lem5780199 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term119 A B s f P op p' q'.
Proof. exact (@lem5780198 A B s f P op p' q'). Qed.
Lemma lem5780200 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : (term119 A B s f P op p' q') = (term120 A B s f P op p' q').
Proof. exact (eq_refl (term119 A B s f P op p' q')). Qed.
Lemma lem5780201 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (p' : Prop) (q' : Prop) : term120 A B s f P op p' q'.
Proof. exact (EQ_MP (@lem5780200 A B s f P op p' q') (@lem5780199 A B s f P op p' q')). Qed.
Lemma lem5780229 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term51 A B op s P f) = (term51 A B op s P f).
Proof. exact (eq_refl (term51 A B op s P f)). Qed.
Lemma lem5780230 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term121 A B op s P f q'.
Proof. exact (@lem5780201 A B s f P op (term51 A B op s P f) q'). Qed.
Lemma lem5780231 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term122 A B op s P f q'.
Proof. exact (@lem5780230 A B op s P f q' (@lem5780229 A B op s P f)). Qed.
Lemma lem5780246 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term37 B P op) = True.
Proof. exact (EQ_MP (@lem5780116 B P op) (@lem5780115 B P op h1)). Qed.
Lemma lem5780247 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term123 A B s f P op.
Proof. exact (fun h0 : term51 A B op s P f => @lem5780246 B P op h1). Qed.
Lemma lem5780248 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term124 A B op s P f.
Proof. exact (@lem5780231 A B op s P f True). Qed.
Lemma lem5780249 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term109 A B s f P op) = (term125 A B op s P f).
Proof. exact (@lem5780248 A B op s P f (@lem5780247 A B s f P op h1)). Qed.
Lemma lem5780251 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780252 {A B : Type'} (op : type1400 B) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term125 A B op s P f) = True.
Proof. exact (@lem5780251 (term51 A B op s P f)). Qed.
Lemma lem5780253 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term109 A B s f P op) = True.
Proof. exact (TRANS (@lem5780249 A B s f P op h1) (@lem5780252 A B op s P f)). Qed.
Lemma lem5780254 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term126 A B s f P op.
Proof. exact (fun h0 : term36 B P op => @lem5780253 A B s f P op h1). Qed.
Lemma lem5780255 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term127 A B s f P op.
Proof. exact (@lem5780172 A B s f P op True). Qed.
Lemma lem5780256 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term101 A B s f P op) = (term128 B P op).
Proof. exact (@lem5780255 A B s f P op (@lem5780254 A B s f P op h1)). Qed.
Lemma lem5780258 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780259 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term128 B P op) = True.
Proof. exact (@lem5780258 (term36 B P op)). Qed.
Lemma lem5780260 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term101 A B s f P op) = True.
Proof. exact (TRANS (@lem5780256 A B s f P op h1) (@lem5780259 B P op)). Qed.
Lemma lem5780261 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term129 A B s f P op.
Proof. exact (fun h0 : term37 B P op => @lem5780260 A B s f P op h0). Qed.
Lemma lem5780262 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term130 A B s f P op.
Proof. exact (@lem5780114 A B s f P op True). Qed.
Lemma lem5780263 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term93 A B s f P op) = (term131 B P op).
Proof. exact (@lem5780262 A B s f P op (@lem5780261 A B s f P op)). Qed.
Lemma lem5780265 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780266 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term131 B P op) = True.
Proof. exact (@lem5780265 (term37 B P op)). Qed.
Lemma lem5780267 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term93 A B s f P op) = True.
Proof. exact (TRANS (@lem5780263 A B s f P op) (@lem5780266 B P op)). Qed.
Lemma lem5780268 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term132 A B s f P op.
Proof. exact (fun h0 : @monoidal B op => @lem5780267 A B s f P op). Qed.
Lemma lem5780269 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term133 A B s f P op.
Proof. exact (@lem5780095 A B s f P op True). Qed.
Lemma lem5780270 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term75 A B s f P op) = (term134 B op).
Proof. exact (@lem5780269 A B s f P op (@lem5780268 A B s f P op)). Qed.
Lemma lem5780272 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780273 {B : Type'} (op : type1400 B) : (term134 B op) = True.
Proof. exact (@lem5780272 (@monoidal B op)). Qed.
Lemma lem5780274 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : (term75 A B s f P op) = True.
Proof. exact (TRANS (@lem5780270 A B s f P op) (@lem5780273 B op)). Qed.
Lemma lem5780275 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : True = (term75 A B s f P op).
Proof. exact (SYM (@lem5780274 A B s f P op)). Qed.
Lemma lem5780278 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem5778684 A P) (@lem5778683 A P)). Qed.
Lemma lem5780279 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (@lem5780278 A P). Qed.
Lemma lem5780280 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term135 A B P op f.
Proof. exact (@lem5780279 A (term136 A B P op f)). Qed.
Lemma lem5780281 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term137 A B P op f) = (term138 A B P op f).
Proof. exact (eq_refl (term137 A B P op f)). Qed.
Lemma lem5780282 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5780283 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term139 A B P op f) = (term140 A B P op f).
Proof. exact (MK_COMB (@lem5780282) (@lem5780281 A B P op f)). Qed.
Lemma lem5780284 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term141 A B P op f s) = (term142 A B P op s f).
Proof. exact (eq_refl (term141 A B P op f s)). Qed.
Lemma lem5780285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5780286 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term143 A B P op f s) = (term144 A B P op s f).
Proof. exact (MK_COMB (@lem5780285) (@lem5780284 A B P op s f)). Qed.
Lemma lem5780287 {A : Type'} (x : A) (s : A -> Prop) : (term145 A x s) = (term145 A x s).
Proof. exact (eq_refl (term145 A x s)). Qed.
Lemma lem5780288 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term146 A B P op f x s) = (term147 A B P op f x s).
Proof. exact (MK_COMB (@lem5780286 A B P op s f) (@lem5780287 A x s)). Qed.
Lemma lem5780289 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5780290 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term148 A B P op f x s) = (term149 A B P op f x s).
Proof. exact (MK_COMB (@lem5780289) (@lem5780288 A B P op f x s)). Qed.
Lemma lem5780291 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term150 A B P op f x s) = (term151 A B P op x s f).
Proof. exact (eq_refl (term150 A B P op f x s)). Qed.
Lemma lem5780292 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term152 A B P op f x s) = (term153 A B P op x s f).
Proof. exact (MK_COMB (@lem5780290 A B P op f x s) (@lem5780291 A B P op x s f)). Qed.
Lemma lem5780293 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term154 A B P op f x) = (term155 A B P op x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5780292 A B P op x s f)). Qed.
Lemma lem5780294 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5780295 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term156 A B P op f x) = (term157 A B P op x f).
Proof. exact (MK_COMB (@lem5780294 A) (@lem5780293 A B P op x f)). Qed.
Lemma lem5780296 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term158 A B P op f) = (term159 A B P op f).
Proof. exact (fun_ext (fun x : A => @lem5780295 A B P op x f)). Qed.
Lemma lem5780297 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5780298 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term160 A B P op f) = (term161 A B P op f).
Proof. exact (MK_COMB (@lem5780297 A) (@lem5780296 A B P op f)). Qed.
Lemma lem5780299 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term162 A B P op f) = (term163 A B P op f).
Proof. exact (MK_COMB (@lem5780283 A B P op f) (@lem5780298 A B P op f)). Qed.
Lemma lem5780300 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5780301 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term164 A B P op f) = (term165 A B P op f).
Proof. exact (MK_COMB (@lem5780300) (@lem5780299 A B P op f)). Qed.
Lemma lem5780302 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term141 A B P op f s) = (term142 A B P op s f).
Proof. exact (eq_refl (term141 A B P op f s)). Qed.
Lemma lem5780303 {A : Type'} (s : A -> Prop) : (term166 A s) = (term166 A s).
Proof. exact (eq_refl (term166 A s)). Qed.
Lemma lem5780304 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term167 A B P op f s) = (term168 A B P op s f).
Proof. exact (MK_COMB (@lem5780303 A s) (@lem5780302 A B P op s f)). Qed.
Lemma lem5780305 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term169 A B P op f) = (term170 A B P op f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5780304 A B P op s f)). Qed.
Lemma lem5780306 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5780307 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term171 A B P op f) = (term172 A B P op f).
Proof. exact (MK_COMB (@lem5780306 A) (@lem5780305 A B P op f)). Qed.
Lemma lem5780308 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term135 A B P op f) = (term173 A B P op f).
Proof. exact (MK_COMB (@lem5780301 A B P op f) (@lem5780307 A B P op f)). Qed.
Lemma lem5780309 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term173 A B P op f.
Proof. exact (EQ_MP (@lem5780308 A B P op f) (@lem5780280 A B P op f)). Qed.
Lemma lem5780310 {A : Type'} (x : A) : term174 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem5780311 {A : Type'} (x : A) : (term174 A x) = (term175 A x).
Proof. exact (eq_refl (term174 A x)). Qed.
Lemma lem5780312 {A : Type'} (x : A) : term175 A x.
Proof. exact (EQ_MP (@lem5780311 A x) (@lem5780310 A x)). Qed.
Lemma lem5780313 {A : Type'} (x : A) (y : A) : term176 A x y.
Proof. exact (@lem5780312 A x y). Qed.
Lemma lem5780314 {A : Type'} (y : A) (x : A) : (term176 A x y) = (term177 A y x).
Proof. exact (eq_refl (term176 A x y)). Qed.
Lemma lem5780315 {A : Type'} (y : A) (x : A) : term177 A y x.
Proof. exact (EQ_MP (@lem5780314 A y x) (@lem5780313 A x y)). Qed.
Lemma lem5780316 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term178 A y x s.
Proof. exact (@lem5780315 A y x s). Qed.
Lemma lem5780317 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term178 A y x s) = ((term179 A x y s) = (term180 A y x s)).
Proof. exact (eq_refl (term178 A y x s)). Qed.
Lemma lem5780325 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term181 _120477 _120519 _120521 op.
Proof. exact (@lem5753565 _120477 _120519 _120521 op). Qed.
Lemma lem5780326 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : (term181 _120477 _120519 _120521 op) = (term182 _120477 _120519 _120521 op).
Proof. exact (eq_refl (term181 _120477 _120519 _120521 op)). Qed.
Lemma lem5780327 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) : term182 _120477 _120519 _120521 op.
Proof. exact (EQ_MP (@lem5780326 _120477 _120519 _120521 op) (@lem5780325 _120477 _120519 _120521 op)). Qed.
Lemma lem5780328 {_120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : @monoidal _120519 op.
Proof. exact (h1). Qed.
Lemma lem5780329 {_120477 _120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term183 _120477 _120519 _120521 op.
Proof. exact (@lem5780327 _120477 _120519 _120521 op (@lem5780328 _120519 op h1)). Qed.
Lemma lem5780330 {_120519 _120521 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term184 _120519 _120521 op.
Proof. exact (proj2 (@lem5780329 Prop _120519 _120521 op h1)). Qed.
Lemma lem5780331 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term185 _120519 _120521 op f.
Proof. exact (@lem5780330 _120519 _120521 op h1 f). Qed.
Lemma lem5780332 {_120519 _120521 : Type'} (op : type1400 _120519) (f : _120521 -> _120519) : (term185 _120519 _120521 op f) = (term186 _120519 _120521 op f).
Proof. exact (eq_refl (term185 _120519 _120521 op f)). Qed.
Lemma lem5780333 {_120519 _120521 : Type'} (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term186 _120519 _120521 op f.
Proof. exact (EQ_MP (@lem5780332 _120519 _120521 op f) (@lem5780331 _120519 _120521 f op h1)). Qed.
Lemma lem5780334 {_120519 _120521 : Type'} (f : _120521 -> _120519) (x : _120521) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term187 _120519 _120521 op f x.
Proof. exact (@lem5780333 _120519 _120521 f op h1 x). Qed.
Lemma lem5780335 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) : (term187 _120519 _120521 op f x) = (term188 _120519 _120521 x op f).
Proof. exact (eq_refl (term187 _120519 _120521 op f x)). Qed.
Lemma lem5780336 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term188 _120519 _120521 x op f.
Proof. exact (EQ_MP (@lem5780335 _120519 _120521 x op f) (@lem5780334 _120519 _120521 f x op h1)). Qed.
Lemma lem5780337 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term189 _120519 _120521 x op f s.
Proof. exact (@lem5780336 _120519 _120521 x f op h1 s). Qed.
Lemma lem5780338 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term189 _120519 _120521 x op f s) = (term190 _120519 _120521 x op s f).
Proof. exact (eq_refl (term189 _120519 _120521 x op f s)). Qed.
Lemma lem5780339 {_120519 _120521 : Type'} (x : _120521) (s : _120521 -> Prop) (f : _120521 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term190 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5780338 _120519 _120521 x op s f) (@lem5780337 _120519 _120521 x f s op h1)). Qed.
Lemma lem5780340 {_120521 : Type'} (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : @FINITE _120521 s.
Proof. exact (h1). Qed.
Lemma lem5780341 {_120519 _120521 : Type'} (x : _120521) (f : _120521 -> _120519) (s : _120521 -> Prop) (op : type1400 _120519) (h1 : @FINITE _120521 s) (h2 : @monoidal _120519 op) : (term191 _120519 _120521 op x s f) = (term192 _120519 _120521 x op s f).
Proof. exact (@lem5780339 _120519 _120521 x s f op h2 (@lem5780340 _120521 s h1)). Qed.
Lemma lem5780342 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (f : _120521 -> _120519) (s : _120521 -> Prop) (h1 : @FINITE _120521 s) : term193 _120519 _120521 x op s f.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5780341 _120519 _120521 x f s op h1 h0). Qed.
Lemma lem5780343 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term194 _120519 _120521 x op s f.
Proof. exact (fun h0 : @FINITE _120521 s => @lem5780342 _120519 _120521 x op f s h0). Qed.
Lemma lem5780345 (p : Prop) (q : Prop) (r : Prop) : (term195 p q r) = (term196 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5780350 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : (term194 _120519 _120521 x op s f) = (term197 _120519 _120521 x op s f).
Proof. exact (@lem5780345 (@FINITE _120521 s) (@monoidal _120519 op) ((term191 _120519 _120521 op x s f) = (term192 _120519 _120521 x op s f))). Qed.
Lemma lem5780352 {_120477 _120519 : Type'} (op : type1400 _120519) (h1 : @monoidal _120519 op) : term198 _120477 _120519 op.
Proof. exact (proj1 (@lem5780329 _120477 _120519 Prop op h1)). Qed.
Lemma lem5780353 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : term199 _120477 _120519 op f.
Proof. exact (@lem5780352 _120477 _120519 op h1 f). Qed.
Lemma lem5780354 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : (term199 _120477 _120519 op f) = ((@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op)).
Proof. exact (eq_refl (term199 _120477 _120519 op f)). Qed.
Lemma lem5780355 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) (h1 : @monoidal _120519 op) : (@iterate _120519 _120477 op (@EMPTY _120477) f) = (@neutral _120519 op).
Proof. exact (EQ_MP (@lem5780354 _120477 _120519 f op) (@lem5780353 _120477 _120519 f op h1)). Qed.
Lemma lem5780366 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780367 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780366 p q p' q'). Qed.
Lemma lem5780368 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780367 p q p'). Qed.
Lemma lem5780369 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term200 A B P op f.
Proof. exact (@lem5780368 (@monoidal B op) (term201 A B P op f)). Qed.
Lemma lem5780370 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term202 A B P op f p'.
Proof. exact (@lem5780369 A B P op f p'). Qed.
Lemma lem5780371 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : (term202 A B P op f p') = (term203 A B P op f p').
Proof. exact (eq_refl (term202 A B P op f p')). Qed.
Lemma lem5780372 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term203 A B P op f p'.
Proof. exact (EQ_MP (@lem5780371 A B P op f p') (@lem5780370 A B P op f p')). Qed.
Lemma lem5780373 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term204 A B P op f p' q'.
Proof. exact (@lem5780372 A B P op f p' q'). Qed.
Lemma lem5780374 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : (term204 A B P op f p' q') = (term205 A B P op f p' q').
Proof. exact (eq_refl (term204 A B P op f p' q')). Qed.
Lemma lem5780375 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term205 A B P op f p' q'.
Proof. exact (EQ_MP (@lem5780374 A B P op f p' q') (@lem5780373 A B P op f p' q')). Qed.
Lemma lem5780376 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@monoidal B op).
Proof. exact (eq_refl (@monoidal B op)). Qed.
Lemma lem5780377 {A B : Type'} (P : B -> Prop) (f : A -> B) (op : type1400 B) (q' : Prop) : term206 A B P f op q'.
Proof. exact (@lem5780375 A B P op f (@monoidal B op) q'). Qed.
Lemma lem5780378 {A B : Type'} (P : B -> Prop) (f : A -> B) (op : type1400 B) (q' : Prop) : term207 A B P f op q'.
Proof. exact (@lem5780377 A B P f op q' (@lem5780376 B op)). Qed.
Lemma lem5780379 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5780380 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5780385 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780386 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780385 p q p' q'). Qed.
Lemma lem5780387 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780386 p q p'). Qed.
Lemma lem5780388 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term208 A B P op f.
Proof. exact (@lem5780387 (term37 B P op) (term209 A B P op f)). Qed.
Lemma lem5780389 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term210 A B P op f p'.
Proof. exact (@lem5780388 A B P op f p'). Qed.
Lemma lem5780390 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : (term210 A B P op f p') = (term211 A B P op f p').
Proof. exact (eq_refl (term210 A B P op f p')). Qed.
Lemma lem5780391 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term211 A B P op f p'.
Proof. exact (EQ_MP (@lem5780390 A B P op f p') (@lem5780389 A B P op f p')). Qed.
Lemma lem5780392 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term212 A B P op f p' q'.
Proof. exact (@lem5780391 A B P op f p' q'). Qed.
Lemma lem5780393 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : (term212 A B P op f p' q') = (term213 A B P op f p' q').
Proof. exact (eq_refl (term212 A B P op f p' q')). Qed.
Lemma lem5780394 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term213 A B P op f p' q'.
Proof. exact (EQ_MP (@lem5780393 A B P op f p' q') (@lem5780392 A B P op f p' q')). Qed.
Lemma lem5780395 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term37 B P op) = (term37 B P op).
Proof. exact (eq_refl (term37 B P op)). Qed.
Lemma lem5780396 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term214 A B f P op q'.
Proof. exact (@lem5780394 A B P op f (term37 B P op) q'). Qed.
Lemma lem5780397 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term215 A B f P op q'.
Proof. exact (@lem5780396 A B f P op q' (@lem5780395 B P op)). Qed.
Lemma lem5780398 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term37 B P op.
Proof. exact (h1). Qed.
Lemma lem5780399 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term37 B P op) = ((term37 B P op) = True).
Proof. exact (@lem7 (term37 B P op)). Qed.
Lemma lem5780404 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780405 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780404 p q p' q'). Qed.
Lemma lem5780406 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780405 p q p'). Qed.
Lemma lem5780407 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term216 A B P op f.
Proof. exact (@lem5780406 (term36 B P op) (term217 A B P op f)). Qed.
Lemma lem5780408 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term218 A B P op f p'.
Proof. exact (@lem5780407 A B P op f p'). Qed.
Lemma lem5780409 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : (term218 A B P op f p') = (term219 A B P op f p').
Proof. exact (eq_refl (term218 A B P op f p')). Qed.
Lemma lem5780410 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term219 A B P op f p'.
Proof. exact (EQ_MP (@lem5780409 A B P op f p') (@lem5780408 A B P op f p')). Qed.
Lemma lem5780411 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term220 A B P op f p' q'.
Proof. exact (@lem5780410 A B P op f p' q'). Qed.
Lemma lem5780412 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : (term220 A B P op f p' q') = (term221 A B P op f p' q').
Proof. exact (eq_refl (term220 A B P op f p' q')). Qed.
Lemma lem5780413 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term221 A B P op f p' q'.
Proof. exact (EQ_MP (@lem5780412 A B P op f p' q') (@lem5780411 A B P op f p' q')). Qed.
Lemma lem5780453 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term36 B P op) = (term36 B P op).
Proof. exact (eq_refl (term36 B P op)). Qed.
Lemma lem5780454 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term222 A B f P op q'.
Proof. exact (@lem5780413 A B P op f (term36 B P op) q'). Qed.
Lemma lem5780455 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term223 A B f P op q'.
Proof. exact (@lem5780454 A B f P op q' (@lem5780453 B P op)). Qed.
Lemma lem5780475 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780476 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780475 p q p' q'). Qed.
Lemma lem5780477 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780476 p q p'). Qed.
Lemma lem5780478 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term224 A B P op f.
Proof. exact (@lem5780477 (term225 A B P f) (term226 A B P op f)). Qed.
Lemma lem5780479 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term227 A B P op f p'.
Proof. exact (@lem5780478 A B P op f p'). Qed.
Lemma lem5780480 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : (term227 A B P op f p') = (term228 A B P op f p').
Proof. exact (eq_refl (term227 A B P op f p')). Qed.
Lemma lem5780481 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) : term228 A B P op f p'.
Proof. exact (EQ_MP (@lem5780480 A B P op f p') (@lem5780479 A B P op f p')). Qed.
Lemma lem5780482 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term229 A B P op f p' q'.
Proof. exact (@lem5780481 A B P op f p' q'). Qed.
Lemma lem5780483 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : (term229 A B P op f p' q') = (term230 A B P op f p' q').
Proof. exact (eq_refl (term229 A B P op f p' q')). Qed.
Lemma lem5780484 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (p' : Prop) (q' : Prop) : term230 A B P op f p' q'.
Proof. exact (EQ_MP (@lem5780483 A B P op f p' q') (@lem5780482 A B P op f p' q')). Qed.
Lemma lem5780512 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term225 A B P f) = (term225 A B P f).
Proof. exact (eq_refl (term225 A B P f)). Qed.
Lemma lem5780513 {A B : Type'} (op : type1400 B) (P : B -> Prop) (f : A -> B) (q' : Prop) : term231 A B op P f q'.
Proof. exact (@lem5780484 A B P op f (term225 A B P f) q'). Qed.
Lemma lem5780514 {A B : Type'} (op : type1400 B) (P : B -> Prop) (f : A -> B) (q' : Prop) : term232 A B op P f q'.
Proof. exact (@lem5780513 A B op P f q' (@lem5780512 A B P f)). Qed.
Lemma lem5780529 {_120477 _120519 : Type'} (f : _120477 -> _120519) (op : type1400 _120519) : term233 _120477 _120519 f op.
Proof. exact (fun h0 : @monoidal _120519 op => @lem5780355 _120477 _120519 f op h0). Qed.
Lemma lem5780530 {A B : Type'} (f : A -> B) (op : type1400 B) : term233 A B f op.
Proof. exact (@lem5780529 A B f op). Qed.
Lemma lem5780532 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5780380 B op) (@lem5780379 B op h1)). Qed.
Lemma lem5780533 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : True = (@monoidal B op).
Proof. exact (SYM (@lem5780532 B op h1)). Qed.
Lemma lem5780534 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (EQ_MP (@lem5780533 B op h1) (@lem0)). Qed.
Lemma lem5780535 {A B : Type'} (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (@iterate B A op (@EMPTY A) f) = (@neutral B op).
Proof. exact (@lem5780530 A B f op (@lem5780534 B op h1)). Qed.
Lemma lem5780536 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem5780537 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) : (term226 A B P op f) = (term37 B P op).
Proof. exact (MK_COMB (@lem5780536 B P) (@lem5780535 A B f op h1)). Qed.
Lemma lem5780539 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term37 B P op) = True.
Proof. exact (EQ_MP (@lem5780399 B P op) (@lem5780398 B P op h1)). Qed.
Lemma lem5780540 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : (term226 A B P op f) = True.
Proof. exact (TRANS (@lem5780537 A B f P op h1) (@lem5780539 B P op h2)). Qed.
Lemma lem5780541 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : term234 A B P op f.
Proof. exact (fun h0 : term225 A B P f => @lem5780540 A B f P op h1 h2). Qed.
Lemma lem5780542 {A B : Type'} (op : type1400 B) (P : B -> Prop) (f : A -> B) : term235 A B op P f.
Proof. exact (@lem5780514 A B op P f True). Qed.
Lemma lem5780543 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : (term217 A B P op f) = (term236 A B P f).
Proof. exact (@lem5780542 A B op P f (@lem5780541 A B f P op h1 h2)). Qed.
Lemma lem5780545 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780546 {A B : Type'} (P : B -> Prop) (f : A -> B) : (term236 A B P f) = True.
Proof. exact (@lem5780545 (term225 A B P f)). Qed.
Lemma lem5780547 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : (term217 A B P op f) = True.
Proof. exact (TRANS (@lem5780543 A B f P op h1 h2) (@lem5780546 A B P f)). Qed.
Lemma lem5780548 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : term237 A B P op f.
Proof. exact (fun h0 : term36 B P op => @lem5780547 A B f P op h1 h2). Qed.
Lemma lem5780549 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) : term238 A B f P op.
Proof. exact (@lem5780455 A B f P op True). Qed.
Lemma lem5780550 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : (term209 A B P op f) = (term128 B P op).
Proof. exact (@lem5780549 A B f P op (@lem5780548 A B f P op h1 h2)). Qed.
Lemma lem5780552 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780553 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term128 B P op) = True.
Proof. exact (@lem5780552 (term36 B P op)). Qed.
Lemma lem5780554 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : (term209 A B P op f) = True.
Proof. exact (TRANS (@lem5780550 A B f P op h1 h2) (@lem5780553 B P op)). Qed.
Lemma lem5780555 {A B : Type'} (P : B -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term239 A B P op f.
Proof. exact (fun h0 : term37 B P op => @lem5780554 A B f P op h1 h0). Qed.
Lemma lem5780556 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) : term240 A B f P op.
Proof. exact (@lem5780397 A B f P op True). Qed.
Lemma lem5780557 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) : (term201 A B P op f) = (term131 B P op).
Proof. exact (@lem5780556 A B f P op (@lem5780555 A B P f op h1)). Qed.
Lemma lem5780559 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780560 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term131 B P op) = True.
Proof. exact (@lem5780559 (term37 B P op)). Qed.
Lemma lem5780561 {A B : Type'} (P : B -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : (term201 A B P op f) = True.
Proof. exact (TRANS (@lem5780557 A B f P op h1) (@lem5780560 B P op)). Qed.
Lemma lem5780562 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term241 A B P op f.
Proof. exact (fun h0 : @monoidal B op => @lem5780561 A B P f op h0). Qed.
Lemma lem5780563 {A B : Type'} (P : B -> Prop) (f : A -> B) (op : type1400 B) : term242 A B P f op.
Proof. exact (@lem5780378 A B P f op True). Qed.
Lemma lem5780564 {A B : Type'} (P : B -> Prop) (f : A -> B) (op : type1400 B) : (term138 A B P op f) = (term134 B op).
Proof. exact (@lem5780563 A B P f op (@lem5780562 A B P op f)). Qed.
Lemma lem5780566 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5780567 {B : Type'} (op : type1400 B) : (term134 B op) = True.
Proof. exact (@lem5780566 (@monoidal B op)). Qed.
Lemma lem5780568 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term138 A B P op f) = True.
Proof. exact (TRANS (@lem5780564 A B P f op) (@lem5780567 B op)). Qed.
Lemma lem5780569 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5780570 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term140 A B P op f) = (and True).
Proof. exact (MK_COMB (@lem5780569) (@lem5780568 A B P op f)). Qed.
Lemma lem5780582 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5780583 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5780582 p q p' q'). Qed.
Lemma lem5780584 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5780583 p q p'). Qed.
Lemma lem5780585 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : term243 A B P op x s f.
Proof. exact (@lem5780584 (term147 A B P op f x s) (term151 A B P op x s f)). Qed.
Lemma lem5780586 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term244 A B P op x s f p'.
Proof. exact (@lem5780585 A B P op x s f p'). Qed.
Lemma lem5780587 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term244 A B P op x s f p') = (term245 A B P op x s f p').
Proof. exact (eq_refl (term244 A B P op x s f p')). Qed.
Lemma lem5780588 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term245 A B P op x s f p'.
Proof. exact (EQ_MP (@lem5780587 A B P op x s f p') (@lem5780586 A B P op x s f p')). Qed.
Lemma lem5780589 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term246 A B P op x s f p' q'.
Proof. exact (@lem5780588 A B P op x s f p' q'). Qed.
Lemma lem5780590 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term246 A B P op x s f p' q') = (term247 A B P op x s f p' q').
Proof. exact (eq_refl (term246 A B P op x s f p' q')). Qed.
Lemma lem5780591 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term247 A B P op x s f p' q'.
Proof. exact (EQ_MP (@lem5780590 A B P op x s f p' q') (@lem5780589 A B P op x s f p' q')). Qed.
Lemma lem5781817 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term147 A B P op f x s) = (term147 A B P op f x s).
Proof. exact (eq_refl (term147 A B P op f x s)). Qed.
Lemma lem5781818 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term248 A B P op f x s q'.
Proof. exact (@lem5780591 A B P op x s f (term147 A B P op f x s) q'). Qed.
Lemma lem5781819 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (q' : Prop) : term249 A B P op f x s q'.
Proof. exact (@lem5781818 A B P op f x s q' (@lem5781817 A B P op f x s)). Qed.
Lemma lem5781820 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term147 A B P op f x s.
Proof. exact (h1). Qed.
Lemma lem5781821 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term145 A x s.
Proof. exact (proj2 (@lem5781820 A B P op f x s h1)). Qed.
Lemma lem5781822 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : @FINITE A s.
Proof. exact (proj2 (@lem5781821 A B P op f x s h1)). Qed.
Lemma lem5781823 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem5781825 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term250 A x s.
Proof. exact (proj1 (@lem5781821 A B P op f x s h1)). Qed.
Lemma lem5781826 {A : Type'} (x : A) (s : A -> Prop) : term251 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem5781828 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term142 A B P op s f.
Proof. exact (proj1 (@lem5781820 A B P op f x s h1)). Qed.
Lemma lem5781829 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5781830 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : term252 A B P op s f.
Proof. exact (@lem5781828 A B P op f x s h2 (@lem5781829 B op h1)). Qed.
Lemma lem5781831 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term37 B P op.
Proof. exact (h1). Qed.
Lemma lem5781832 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term37 B P op) (h3 : term147 A B P op f x s) : term253 A B P op s f.
Proof. exact (@lem5781830 A B P op f x s h1 h3 (@lem5781831 B P op h2)). Qed.
Lemma lem5781833 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term36 B P op.
Proof. exact (h1). Qed.
Lemma lem5781834 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) (h4 : term147 A B P op f x s) : term254 A B P op s f.
Proof. exact (@lem5781832 A B P op f x s h2 h3 h4 (@lem5781833 B P op h1)). Qed.
Lemma lem5781835 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term255 A B s P f) : term255 A B s P f.
Proof. exact (h1). Qed.
Lemma lem5781836 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term255 A B s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : term40 A B P op s f.
Proof. exact (@lem5781834 A B P op f x s h2 h3 h4 h5 (@lem5781835 A B s P f h1)). Qed.
Lemma lem5781837 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term40 A B P op s f) = ((term40 A B P op s f) = True).
Proof. exact (@lem7 (term40 A B P op s f)). Qed.
Lemma lem5781838 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term255 A B s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : (term40 A B P op s f) = True.
Proof. exact (EQ_MP (@lem5781837 A B P op s f) (@lem5781836 A B P op f x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5781839 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term255 A B s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term147 A B P op f x s) : term256 A B P op s f.
Proof. exact (fun h0 : term37 B P op => @lem5781838 A B P op f x s h1 h2 h3 h0 h4). Qed.
Lemma lem5781840 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term255 A B s P f) (h2 : term36 B P op) (h3 : term147 A B P op f x s) : term257 A B P op s f.
Proof. exact (fun h0 : @monoidal B op => @lem5781839 A B P op f x s h1 h2 h0 h3). Qed.
Lemma lem5781841 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term255 A B s P f) (h2 : term147 A B P op f x s) : term258 A B P op s f.
Proof. exact (fun h0 : term36 B P op => @lem5781840 A B P op f x s h1 h0 h2). Qed.
Lemma lem5781842 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term259 A B P op s f.
Proof. exact (fun h0 : term255 A B s P f => @lem5781841 A B P op f x s h0 h1). Qed.
Lemma lem5781844 (p : Prop) (q : Prop) (r : Prop) : (term195 p q r) = (term196 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5781845 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term259 A B P op s f) = (term260 A B P op s f).
Proof. exact (@lem5781844 (term255 A B s P f) (term36 B P op) (term257 A B P op s f)). Qed.
Lemma lem5781847 (p : Prop) (q : Prop) (r : Prop) : (term195 p q r) = (term196 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5781848 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term260 A B P op s f) = (term261 A B P op s f).
Proof. exact (@lem5781847 (term262 A B s f P op) (@monoidal B op) (term256 A B P op s f)). Qed.
Lemma lem5781850 (p : Prop) (q : Prop) (r : Prop) : (term195 p q r) = (term196 p q r).
Proof. exact (EQ_MP (@lem197 p q r) (@lem196 p q r)). Qed.
Lemma lem5781855 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term261 A B P op s f) = (term263 A B P op s f).
Proof. exact (@lem5781850 (term264 A B s f P op) (term37 B P op) ((term40 A B P op s f) = True)). Qed.
Lemma lem5781856 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term260 A B P op s f) = (term263 A B P op s f).
Proof. exact (TRANS (@lem5781848 A B P op s f) (@lem5781855 A B P op s f)). Qed.
Lemma lem5781857 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term259 A B P op s f) = (term263 A B P op s f).
Proof. exact (TRANS (@lem5781845 A B P op s f) (@lem5781856 A B P op s f)). Qed.
Lemma lem5781862 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5781863 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5781862 p q p' q'). Qed.
Lemma lem5781864 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5781863 p q p'). Qed.
Lemma lem5781865 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : term265 A B P op x s f.
Proof. exact (@lem5781864 (@monoidal B op) (term266 A B P op x s f)). Qed.
Lemma lem5781866 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term267 A B P op x s f p'.
Proof. exact (@lem5781865 A B P op x s f p'). Qed.
Lemma lem5781867 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term267 A B P op x s f p') = (term268 A B P op x s f p').
Proof. exact (eq_refl (term267 A B P op x s f p')). Qed.
Lemma lem5781868 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term268 A B P op x s f p'.
Proof. exact (EQ_MP (@lem5781867 A B P op x s f p') (@lem5781866 A B P op x s f p')). Qed.
Lemma lem5781869 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term269 A B P op x s f p' q'.
Proof. exact (@lem5781868 A B P op x s f p' q'). Qed.
Lemma lem5781870 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term269 A B P op x s f p' q') = (term270 A B P op x s f p' q').
Proof. exact (eq_refl (term269 A B P op x s f p' q')). Qed.
Lemma lem5781871 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term270 A B P op x s f p' q'.
Proof. exact (EQ_MP (@lem5781870 A B P op x s f p' q') (@lem5781869 A B P op x s f p' q')). Qed.
Lemma lem5781872 {B : Type'} (op : type1400 B) : (@monoidal B op) = (@monoidal B op).
Proof. exact (eq_refl (@monoidal B op)). Qed.
Lemma lem5781873 {A B : Type'} (P : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (q' : Prop) : term271 A B P x s f op q'.
Proof. exact (@lem5781871 A B P op x s f (@monoidal B op) q'). Qed.
Lemma lem5781874 {A B : Type'} (P : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) (q' : Prop) : term272 A B P x s f op q'.
Proof. exact (@lem5781873 A B P x s f op q' (@lem5781872 B op)). Qed.
Lemma lem5781875 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : @monoidal B op.
Proof. exact (h1). Qed.
Lemma lem5781876 {B : Type'} (op : type1400 B) : (@monoidal B op) = ((@monoidal B op) = True).
Proof. exact (@lem7 (@monoidal B op)). Qed.
Lemma lem5781881 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5781882 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5781881 p q p' q'). Qed.
Lemma lem5781883 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5781882 p q p'). Qed.
Lemma lem5781884 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : term273 A B P op x s f.
Proof. exact (@lem5781883 (term37 B P op) (term274 A B P op x s f)). Qed.
Lemma lem5781885 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term275 A B P op x s f p'.
Proof. exact (@lem5781884 A B P op x s f p'). Qed.
Lemma lem5781886 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term275 A B P op x s f p') = (term276 A B P op x s f p').
Proof. exact (eq_refl (term275 A B P op x s f p')). Qed.
Lemma lem5781887 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term276 A B P op x s f p'.
Proof. exact (EQ_MP (@lem5781886 A B P op x s f p') (@lem5781885 A B P op x s f p')). Qed.
Lemma lem5781888 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term277 A B P op x s f p' q'.
Proof. exact (@lem5781887 A B P op x s f p' q'). Qed.
Lemma lem5781889 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term277 A B P op x s f p' q') = (term278 A B P op x s f p' q').
Proof. exact (eq_refl (term277 A B P op x s f p' q')). Qed.
Lemma lem5781890 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term278 A B P op x s f p' q'.
Proof. exact (EQ_MP (@lem5781889 A B P op x s f p' q') (@lem5781888 A B P op x s f p' q')). Qed.
Lemma lem5781891 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term37 B P op) = (term37 B P op).
Proof. exact (eq_refl (term37 B P op)). Qed.
Lemma lem5781892 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term279 A B x s f P op q'.
Proof. exact (@lem5781890 A B P op x s f (term37 B P op) q'). Qed.
Lemma lem5781893 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term280 A B x s f P op q'.
Proof. exact (@lem5781892 A B x s f P op q' (@lem5781891 B P op)). Qed.
Lemma lem5781894 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : term37 B P op.
Proof. exact (h1). Qed.
Lemma lem5781895 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term37 B P op) = ((term37 B P op) = True).
Proof. exact (@lem7 (term37 B P op)). Qed.
Lemma lem5781900 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5781901 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5781900 p q p' q'). Qed.
Lemma lem5781902 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5781901 p q p'). Qed.
Lemma lem5781903 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : term281 A B P op x s f.
Proof. exact (@lem5781902 (term36 B P op) (term282 A B P op x s f)). Qed.
Lemma lem5781904 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term283 A B P op x s f p'.
Proof. exact (@lem5781903 A B P op x s f p'). Qed.
Lemma lem5781905 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term283 A B P op x s f p') = (term284 A B P op x s f p').
Proof. exact (eq_refl (term283 A B P op x s f p')). Qed.
Lemma lem5781906 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term284 A B P op x s f p'.
Proof. exact (EQ_MP (@lem5781905 A B P op x s f p') (@lem5781904 A B P op x s f p')). Qed.
Lemma lem5781907 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term285 A B P op x s f p' q'.
Proof. exact (@lem5781906 A B P op x s f p' q'). Qed.
Lemma lem5781908 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term285 A B P op x s f p' q') = (term286 A B P op x s f p' q').
Proof. exact (eq_refl (term285 A B P op x s f p' q')). Qed.
Lemma lem5781909 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term286 A B P op x s f p' q'.
Proof. exact (EQ_MP (@lem5781908 A B P op x s f p' q') (@lem5781907 A B P op x s f p' q')). Qed.
Lemma lem5781949 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term36 B P op) = (term36 B P op).
Proof. exact (eq_refl (term36 B P op)). Qed.
Lemma lem5781950 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term287 A B x s f P op q'.
Proof. exact (@lem5781909 A B P op x s f (term36 B P op) q'). Qed.
Lemma lem5781951 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (q' : Prop) : term288 A B x s f P op q'.
Proof. exact (@lem5781950 A B x s f P op q' (@lem5781949 B P op)). Qed.
Lemma lem5781952 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term36 B P op.
Proof. exact (h1). Qed.
Lemma lem5781953 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term289 B P op x.
Proof. exact (@lem5781952 B P op h1 x). Qed.
Lemma lem5781954 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) : (term289 B P op x) = (term290 B P op x).
Proof. exact (eq_refl (term289 B P op x)). Qed.
Lemma lem5781955 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term290 B P op x.
Proof. exact (EQ_MP (@lem5781954 B P op x) (@lem5781953 B x P op h1)). Qed.
Lemma lem5781956 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term291 B P op x y.
Proof. exact (@lem5781955 B x P op h1 y). Qed.
Lemma lem5781957 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) : (term291 B P op x y) = (term292 B P op x y).
Proof. exact (eq_refl (term291 B P op x y)). Qed.
Lemma lem5781958 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term292 B P op x y.
Proof. exact (EQ_MP (@lem5781957 B P op x y) (@lem5781956 B x y P op h1)). Qed.
Lemma lem5781959 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : term293 B x P y.
Proof. exact (h1). Qed.
Lemma lem5781960 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (h1 : term36 B P op) (h2 : term293 B x P y) : term294 B P op x y.
Proof. exact (@lem5781958 B x y P op h1 (@lem5781959 B x P y h2)). Qed.
Lemma lem5781961 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) : (term294 B P op x y) = ((term294 B P op x y) = True).
Proof. exact (@lem7 (term294 B P op x y)). Qed.
Lemma lem5781962 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (h1 : term36 B P op) (h2 : term293 B x P y) : (term294 B P op x y) = True.
Proof. exact (EQ_MP (@lem5781961 B P op x y) (@lem5781960 B op x P y h1 h2)). Qed.
Lemma lem5781971 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5781972 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5781971 p q p' q'). Qed.
Lemma lem5781973 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5781972 p q p'). Qed.
Lemma lem5781974 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : term295 A B P op x s f.
Proof. exact (@lem5781973 (term296 A B x s P f) (term297 A B P op x s f)). Qed.
Lemma lem5781975 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term298 A B P op x s f p'.
Proof. exact (@lem5781974 A B P op x s f p'). Qed.
Lemma lem5781976 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : (term298 A B P op x s f p') = (term299 A B P op x s f p').
Proof. exact (eq_refl (term298 A B P op x s f p')). Qed.
Lemma lem5781977 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) : term299 A B P op x s f p'.
Proof. exact (EQ_MP (@lem5781976 A B P op x s f p') (@lem5781975 A B P op x s f p')). Qed.
Lemma lem5781978 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term300 A B P op x s f p' q'.
Proof. exact (@lem5781977 A B P op x s f p' q'). Qed.
Lemma lem5781979 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : (term300 A B P op x s f p' q') = (term301 A B P op x s f p' q').
Proof. exact (eq_refl (term300 A B P op x s f p' q')). Qed.
Lemma lem5781980 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) (p' : Prop) (q' : Prop) : term301 A B P op x s f p' q'.
Proof. exact (EQ_MP (@lem5781979 A B P op x s f p' q') (@lem5781978 A B P op x s f p' q')). Qed.
Lemma lem5781988 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5781989 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5781988 p q p' q'). Qed.
Lemma lem5781990 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5781989 p q p'). Qed.
Lemma lem5781991 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : term302 A B x s P f x'.
Proof. exact (@lem5781990 (term179 A x' x s) (term46 A B P f x')). Qed.
Lemma lem5781992 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) : term303 A B x s P f x' p'.
Proof. exact (@lem5781991 A B x s P f x' p'). Qed.
Lemma lem5781993 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) : (term303 A B x s P f x' p') = (term304 A B x s P f x' p').
Proof. exact (eq_refl (term303 A B x s P f x' p')). Qed.
Lemma lem5781994 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) : term304 A B x s P f x' p'.
Proof. exact (EQ_MP (@lem5781993 A B x s P f x' p') (@lem5781992 A B x s P f x' p')). Qed.
Lemma lem5781995 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term305 A B x s P f x' p' q'.
Proof. exact (@lem5781994 A B x s P f x' p' q'). Qed.
Lemma lem5781996 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) (q' : Prop) : (term305 A B x s P f x' p' q') = (term306 A B x s P f x' p' q').
Proof. exact (eq_refl (term305 A B x s P f x' p' q')). Qed.
Lemma lem5781997 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) (p' : Prop) (q' : Prop) : term306 A B x s P f x' p' q'.
Proof. exact (EQ_MP (@lem5781996 A B x s P f x' p' q') (@lem5781995 A B x s P f x' p' q')). Qed.
Lemma lem5781999 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term179 A x y s) = (term180 A y x s).
Proof. exact (EQ_MP (@lem5780317 A y x s) (@lem5780316 A y x s)). Qed.
Lemma lem5782000 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term179 A x y s) = (term180 A y x s).
Proof. exact (@lem5781999 A y x s). Qed.
Lemma lem5782001 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term179 A x' x s) = (term180 A x x' s).
Proof. exact (@lem5782000 A x x' s). Qed.
Lemma lem5782006 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term307 A B P f x x' s q'.
Proof. exact (@lem5781997 A B x s P f x' (term180 A x x' s) q'). Qed.
Lemma lem5782007 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (x' : A) (s : A -> Prop) (q' : Prop) : term308 A B P f x x' s q'.
Proof. exact (@lem5782006 A B P f x x' s q' (@lem5782001 A x x' s)). Qed.
Lemma lem5782011 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term46 A B P f x') = (term46 A B P f x').
Proof. exact (eq_refl (term46 A B P f x')). Qed.
Lemma lem5782012 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : term309 A B x s P f x'.
Proof. exact (fun h0 : term180 A x x' s => @lem5782011 A B P f x'). Qed.
Lemma lem5782013 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : term310 A B x s P f x'.
Proof. exact (@lem5782007 A B P f x x' s (term46 A B P f x')). Qed.
Lemma lem5782014 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term311 A B x s P f x') = (term312 A B x s P f x').
Proof. exact (@lem5782013 A B x s P f x' (@lem5782012 A B x s P f x')). Qed.
Lemma lem5782046 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term313 A B x s P f) = (term314 A B x s P f).
Proof. exact (fun_ext (fun x' : A => @lem5782014 A B x s P f x')). Qed.
Lemma lem5782078 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5782079 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term296 A B x s P f) = (term315 A B x s P f).
Proof. exact (MK_COMB (@lem5782078 A) (@lem5782046 A B x s P f)). Qed.
Lemma lem5782115 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term316 A B op x s P f q'.
Proof. exact (@lem5781980 A B P op x s f (term315 A B x s P f) q'). Qed.
Lemma lem5782116 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (q' : Prop) : term317 A B op x s P f q'.
Proof. exact (@lem5782115 A B op x s P f q' (@lem5782079 A B x s P f)). Qed.
Lemma lem5782117 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term315 A B x s P f.
Proof. exact (h1). Qed.
Lemma lem5782118 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term318 A B x s P f x'.
Proof. exact (@lem5782117 A B x s P f h1 x'). Qed.
Lemma lem5782119 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (x' : A) : (term318 A B x s P f x') = (term312 A B x s P f x').
Proof. exact (eq_refl (term318 A B x s P f x')). Qed.
Lemma lem5782120 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term312 A B x s P f x'.
Proof. exact (EQ_MP (@lem5782119 A B x s P f x') (@lem5782118 A B x' x s P f h1)). Qed.
Lemma lem5782121 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (h1 : term180 A x x' s) : term180 A x x' s.
Proof. exact (h1). Qed.
Lemma lem5782122 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (x' : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term180 A x x' s) : term46 A B P f x'.
Proof. exact (@lem5782120 A B x' x s P f h1 (@lem5782121 A x x' s h2)). Qed.
Lemma lem5782123 {A B : Type'} (P : B -> Prop) (f : A -> B) (x' : A) : (term46 A B P f x') = ((term46 A B P f x') = True).
Proof. exact (@lem7 (term46 A B P f x')). Qed.
Lemma lem5782124 {A B : Type'} (P : B -> Prop) (f : A -> B) (x : A) (x' : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term180 A x x' s) : (term46 A B P f x') = True.
Proof. exact (EQ_MP (@lem5782123 A B P f x') (@lem5782122 A B P f x x' s h1 h2)). Qed.
Lemma lem5782131 {_120519 _120521 : Type'} (x : _120521) (op : type1400 _120519) (s : _120521 -> Prop) (f : _120521 -> _120519) : term197 _120519 _120521 x op s f.
Proof. exact (EQ_MP (@lem5780350 _120519 _120521 x op s f) (@lem5780343 _120519 _120521 x op s f)). Qed.
Lemma lem5782132 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term319 A B x op s f.
Proof. exact (@lem5782131 B A x op s f). Qed.
Lemma lem5782136 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem5781823 A s) (@lem5781822 A B P op f x s h1)). Qed.
Lemma lem5782137 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782138 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term320 A s) = (and True).
Proof. exact (MK_COMB (@lem5782137) (@lem5782136 A B P op f x s h1)). Qed.
Lemma lem5782140 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5781876 B op) (@lem5781875 B op h1)). Qed.
Lemma lem5782141 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term321 A B s op) = (True /\ True).
Proof. exact (MK_COMB (@lem5782138 A B P op f x s h2) (@lem5782140 B op h1)). Qed.
Lemma lem5782143 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782144 : (True /\ True) = True.
Proof. exact (@lem5782143 True). Qed.
Lemma lem5782145 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term321 A B s op) = True.
Proof. exact (TRANS (@lem5782141 A B P op f x s h1 h2) (@lem5782144)). Qed.
Lemma lem5782146 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : True = (term321 A B s op).
Proof. exact (SYM (@lem5782145 A B P op f x s h1 h2)). Qed.
Lemma lem5782147 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : term321 A B s op.
Proof. exact (EQ_MP (@lem5782146 A B P op f x s h1 h2) (@lem0)). Qed.
Lemma lem5782148 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term322 A B op x s f) = (term323 A B x op s f).
Proof. exact (@lem5782132 A B x op s f (@lem5782147 A B P op f x s h1 h2)). Qed.
Lemma lem5782150 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term324 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem5782151 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term325 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem5782150 _2963 g t e g' t' e'). Qed.
Lemma lem5782152 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term326 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem5782151 _2963 g t e g' t'). Qed.
Lemma lem5782153 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term327 _2963 g t e.
Proof. exact (fun g' : Prop => @lem5782152 _2963 g t e g'). Qed.
Lemma lem5782154 {B : Type'} (g : Prop) (t : B) (e : B) : term327 B g t e.
Proof. exact (@lem5782153 B g t e). Qed.
Lemma lem5782155 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term328 A B x op s f.
Proof. exact (@lem5782154 B (@IN A x s) (@iterate B A op s f) (term329 A B x op s f)). Qed.
Lemma lem5782156 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) : term330 A B x op s f g'.
Proof. exact (@lem5782155 A B x op s f g'). Qed.
Lemma lem5782157 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) : (term330 A B x op s f g') = (term331 A B x op s f g').
Proof. exact (eq_refl (term330 A B x op s f g')). Qed.
Lemma lem5782158 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) : term331 A B x op s f g'.
Proof. exact (EQ_MP (@lem5782157 A B x op s f g') (@lem5782156 A B x op s f g')). Qed.
Lemma lem5782159 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term332 A B x op s f g' t'.
Proof. exact (@lem5782158 A B x op s f g' t'). Qed.
Lemma lem5782160 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : (term332 A B x op s f g' t') = (term333 A B x op s f g' t').
Proof. exact (eq_refl (term332 A B x op s f g' t')). Qed.
Lemma lem5782161 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) : term333 A B x op s f g' t'.
Proof. exact (EQ_MP (@lem5782160 A B x op s f g' t') (@lem5782159 A B x op s f g' t')). Qed.
Lemma lem5782162 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term334 A B x op s f g' t' e'.
Proof. exact (@lem5782161 A B x op s f g' t' e'). Qed.
Lemma lem5782163 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : (term334 A B x op s f g' t' e') = (term335 A B x op s f g' t' e').
Proof. exact (eq_refl (term334 A B x op s f g' t' e')). Qed.
Lemma lem5782164 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (g' : Prop) (t' : B) (e' : B) : term335 A B x op s f g' t' e'.
Proof. exact (EQ_MP (@lem5782163 A B x op s f g' t' e') (@lem5782162 A B x op s f g' t' e')). Qed.
Lemma lem5782166 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (@IN A x s) = False.
Proof. exact (@lem5781826 A x s (@lem5781825 A B P op f x s h1)). Qed.
Lemma lem5782167 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) (t' : B) (e' : B) : term336 A B x op s f t' e'.
Proof. exact (@lem5782164 A B x op s f False t' e'). Qed.
Lemma lem5782168 {A B : Type'} (t' : B) (e' : B) (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term337 A B x op s f t' e'.
Proof. exact (@lem5782167 A B x op s f t' e' (@lem5782166 A B P op f x s h1)). Qed.
Lemma lem5782172 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : (@iterate B A op s f) = (@iterate B A op s f).
Proof. exact (eq_refl (@iterate B A op s f)). Qed.
Lemma lem5782173 {A B : Type'} (op : type1400 B) (s : A -> Prop) (f : A -> B) : term338 A B op s f.
Proof. exact (fun h0 : False => @lem5782172 A B op s f). Qed.
Lemma lem5782174 {A B : Type'} (e' : B) (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term339 A B x op s f e'.
Proof. exact (@lem5782168 A B (@iterate B A op s f) e' P op f x s h1). Qed.
Lemma lem5782175 {A B : Type'} (e' : B) (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term340 A B x op s f e'.
Proof. exact (@lem5782174 A B e' P op f x s h1 (@lem5782173 A B op s f)). Qed.
Lemma lem5782181 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term329 A B x op s f) = (term329 A B x op s f).
Proof. exact (eq_refl (term329 A B x op s f)). Qed.
Lemma lem5782182 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term341 A B x op s f.
Proof. exact (fun h0 : ~ False => @lem5782181 A B x op s f). Qed.
Lemma lem5782183 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term342 A B x op s f.
Proof. exact (@lem5782175 A B (term329 A B x op s f) P op f x s h1). Qed.
Lemma lem5782184 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term323 A B x op s f) = (term343 A B x op s f).
Proof. exact (@lem5782183 A B P op f x s h1 (@lem5782182 A B x op s f)). Qed.
Lemma lem5782186 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem5782187 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem5782186 B t1 t2). Qed.
Lemma lem5782188 {A B : Type'} (x : A) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term343 A B x op s f) = (term329 A B x op s f).
Proof. exact (@lem5782187 B (@iterate B A op s f) (term329 A B x op s f)). Qed.
Lemma lem5782189 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term323 A B x op s f) = (term329 A B x op s f).
Proof. exact (TRANS (@lem5782184 A B P op f x s h1) (@lem5782188 A B x op s f)). Qed.
Lemma lem5782190 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term322 A B op x s f) = (term329 A B x op s f).
Proof. exact (TRANS (@lem5782148 A B P op f x s h1 h2) (@lem5782189 A B P op f x s h2)). Qed.
Lemma lem5782191 {B : Type'} (P : B -> Prop) : P = P.
Proof. exact (eq_refl P). Qed.
Lemma lem5782192 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term297 A B P op x s f) = (term344 A B P x op s f).
Proof. exact (MK_COMB (@lem5782191 B P) (@lem5782190 A B P op f x s h1 h2)). Qed.
Lemma lem5782194 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term345 B P op x y.
Proof. exact (fun h0 : term293 B x P y => @lem5781962 B op x P y h1 h0). Qed.
Lemma lem5782195 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term345 B P op x y.
Proof. exact (@lem5782194 B x y P op h1). Qed.
Lemma lem5782196 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term346 A B P x op s f.
Proof. exact (@lem5782195 B (f x) (@iterate B A op s f) P op h1). Qed.
Lemma lem5782200 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term347 A B x s P f x'.
Proof. exact (fun h0 : term180 A x x' s => @lem5782124 A B P f x x' s h1 h0). Qed.
Lemma lem5782201 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term347 A B x s P f x'.
Proof. exact (@lem5782200 A B x' x s P f h1). Qed.
Lemma lem5782202 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term348 A B s P f x.
Proof. exact (@lem5782201 A B x x s P f h1). Qed.
Lemma lem5782206 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5782207 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem5782206 A x). Qed.
Lemma lem5782208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5782209 {A : Type'} (x : A) : (term349 A x) = (or True).
Proof. exact (MK_COMB (@lem5782208) (@lem5782207 A x)). Qed.
Lemma lem5782211 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (@IN A x s) = False.
Proof. exact (@lem5781826 A x s (@lem5781825 A B P op f x s h1)). Qed.
Lemma lem5782212 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term350 A x s) = (True \/ False).
Proof. exact (MK_COMB (@lem5782209 A x) (@lem5782211 A B P op f x s h1)). Qed.
Lemma lem5782214 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem5782215 : (True \/ False) = True.
Proof. exact (@lem5782214 False). Qed.
Lemma lem5782216 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term350 A x s) = True.
Proof. exact (TRANS (@lem5782212 A B P op f x s h1) (@lem5782215)). Qed.
Lemma lem5782217 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : True = (term350 A x s).
Proof. exact (SYM (@lem5782216 A B P op f x s h1)). Qed.
Lemma lem5782218 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term350 A x s.
Proof. exact (EQ_MP (@lem5782217 A B P op f x s h1) (@lem0)). Qed.
Lemma lem5782219 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term147 A B P op f x s) : (term46 A B P f x) = True.
Proof. exact (@lem5782202 A B x s P f h1 (@lem5782218 A B P op f x s h2)). Qed.
Lemma lem5782220 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782221 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term147 A B P op f x s) : (term351 A B P f x) = (and True).
Proof. exact (MK_COMB (@lem5782220) (@lem5782219 A B P op f x s h1 h2)). Qed.
Lemma lem5782223 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term263 A B P op s f.
Proof. exact (EQ_MP (@lem5781857 A B P op s f) (@lem5781842 A B P op f x s h1)). Qed.
Lemma lem5782288 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5782289 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5782288 p q p' q'). Qed.
Lemma lem5782290 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5782289 p q p'). Qed.
Lemma lem5782291 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) : term352 A B s P f _72876.
Proof. exact (@lem5782290 (@IN A _72876 s) (term46 A B P f _72876)). Qed.
Lemma lem5782292 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) (p' : Prop) : term353 A B s P f _72876 p'.
Proof. exact (@lem5782291 A B s P f _72876 p'). Qed.
Lemma lem5782293 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) (p' : Prop) : (term353 A B s P f _72876 p') = (term354 A B s P f _72876 p').
Proof. exact (eq_refl (term353 A B s P f _72876 p')). Qed.
Lemma lem5782294 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) (p' : Prop) : term354 A B s P f _72876 p'.
Proof. exact (EQ_MP (@lem5782293 A B s P f _72876 p') (@lem5782292 A B s P f _72876 p')). Qed.
Lemma lem5782295 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) (p' : Prop) (q' : Prop) : term355 A B s P f _72876 p' q'.
Proof. exact (@lem5782294 A B s P f _72876 p' q'). Qed.
Lemma lem5782296 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) (p' : Prop) (q' : Prop) : (term355 A B s P f _72876 p' q') = (term356 A B s P f _72876 p' q').
Proof. exact (eq_refl (term355 A B s P f _72876 p' q')). Qed.
Lemma lem5782297 {A B : Type'} (s : A -> Prop) (P : B -> Prop) (f : A -> B) (_72876 : A) (p' : Prop) (q' : Prop) : term356 A B s P f _72876 p' q'.
Proof. exact (EQ_MP (@lem5782296 A B s P f _72876 p' q') (@lem5782295 A B s P f _72876 p' q')). Qed.
Lemma lem5782298 {A : Type'} (_72876 : A) (s : A -> Prop) : (@IN A _72876 s) = (@IN A _72876 s).
Proof. exact (eq_refl (@IN A _72876 s)). Qed.
Lemma lem5782299 {A B : Type'} (P : B -> Prop) (f : A -> B) (_72876 : A) (s : A -> Prop) (q' : Prop) : term357 A B P f _72876 s q'.
Proof. exact (@lem5782297 A B s P f _72876 (@IN A _72876 s) q'). Qed.
Lemma lem5782300 {A B : Type'} (P : B -> Prop) (f : A -> B) (_72876 : A) (s : A -> Prop) (q' : Prop) : term358 A B P f _72876 s q'.
Proof. exact (@lem5782299 A B P f _72876 s q' (@lem5782298 A _72876 s)). Qed.
Lemma lem5782301 {A : Type'} (_72876 : A) (s : A -> Prop) (h1 : @IN A _72876 s) : @IN A _72876 s.
Proof. exact (h1). Qed.
Lemma lem5782302 {A : Type'} (_72876 : A) (s : A -> Prop) : (@IN A _72876 s) = ((@IN A _72876 s) = True).
Proof. exact (@lem7 (@IN A _72876 s)). Qed.
Lemma lem5782305 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term347 A B x s P f x'.
Proof. exact (fun h0 : term180 A x x' s => @lem5782124 A B P f x x' s h1 h0). Qed.
Lemma lem5782306 {A B : Type'} (x' : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term347 A B x s P f x'.
Proof. exact (@lem5782305 A B x' x s P f h1). Qed.
Lemma lem5782307 {A B : Type'} (_72876 : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term347 A B x s P f _72876.
Proof. exact (@lem5782306 A B _72876 x s P f h1). Qed.
Lemma lem5782313 {A : Type'} (_72876 : A) (s : A -> Prop) (h1 : @IN A _72876 s) : (@IN A _72876 s) = True.
Proof. exact (EQ_MP (@lem5782302 A _72876 s) (@lem5782301 A _72876 s h1)). Qed.
Lemma lem5782314 {A : Type'} (_72876 : A) (x : A) : (term359 A _72876 x) = (term359 A _72876 x).
Proof. exact (eq_refl (term359 A _72876 x)). Qed.
Lemma lem5782315 {A : Type'} (x : A) (_72876 : A) (s : A -> Prop) (h1 : @IN A _72876 s) : (term180 A x _72876 s) = (term360 A _72876 x).
Proof. exact (MK_COMB (@lem5782314 A _72876 x) (@lem5782313 A _72876 s h1)). Qed.
Lemma lem5782317 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem5782318 {A : Type'} (_72876 : A) (x : A) : (term360 A _72876 x) = True.
Proof. exact (@lem5782317 (_72876 = x)). Qed.
Lemma lem5782319 {A : Type'} (x : A) (_72876 : A) (s : A -> Prop) (h1 : @IN A _72876 s) : (term180 A x _72876 s) = True.
Proof. exact (TRANS (@lem5782315 A x _72876 s h1) (@lem5782318 A _72876 x)). Qed.
Lemma lem5782320 {A : Type'} (x : A) (_72876 : A) (s : A -> Prop) (h1 : @IN A _72876 s) : True = (term180 A x _72876 s).
Proof. exact (SYM (@lem5782319 A x _72876 s h1)). Qed.
Lemma lem5782321 {A : Type'} (x : A) (_72876 : A) (s : A -> Prop) (h1 : @IN A _72876 s) : term180 A x _72876 s.
Proof. exact (EQ_MP (@lem5782320 A x _72876 s h1) (@lem0)). Qed.
Lemma lem5782322 {A B : Type'} (x : A) (P : B -> Prop) (f : A -> B) (_72876 : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : @IN A _72876 s) : (term46 A B P f _72876) = True.
Proof. exact (@lem5782307 A B _72876 x s P f h1 (@lem5782321 A x _72876 s h2)). Qed.
Lemma lem5782323 {A B : Type'} (_72876 : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : term361 A B s P f _72876.
Proof. exact (fun h0 : @IN A _72876 s => @lem5782322 A B x P f _72876 s h1 h0). Qed.
Lemma lem5782324 {A B : Type'} (P : B -> Prop) (f : A -> B) (_72876 : A) (s : A -> Prop) : term362 A B P f _72876 s.
Proof. exact (@lem5782300 A B P f _72876 s True). Qed.
Lemma lem5782325 {A B : Type'} (_72876 : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : (term363 A B s P f _72876) = (term364 A _72876 s).
Proof. exact (@lem5782324 A B P f _72876 s (@lem5782323 A B _72876 x s P f h1)). Qed.
Lemma lem5782327 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782328 {A : Type'} (_72876 : A) (s : A -> Prop) : (term364 A _72876 s) = True.
Proof. exact (@lem5782327 (@IN A _72876 s)). Qed.
Lemma lem5782329 {A B : Type'} (_72876 : A) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : (term363 A B s P f _72876) = True.
Proof. exact (TRANS (@lem5782325 A B _72876 x s P f h1) (@lem5782328 A _72876 s)). Qed.
Lemma lem5782332 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : (term365 A B s P f) = (term366 A).
Proof. exact (fun_ext (fun _72876 : A => @lem5782329 A B _72876 x s P f h1)). Qed.
Lemma lem5782333 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5782334 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : (term255 A B s P f) = (term367 A).
Proof. exact (MK_COMB (@lem5782333 A) (@lem5782332 A B x s P f h1)). Qed.
Lemma lem5782336 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5782337 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (@lem5782336 A t). Qed.
Lemma lem5782338 {A : Type'} : (term367 A) = True.
Proof. exact (@lem5782337 A True). Qed.
Lemma lem5782339 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : (term255 A B s P f) = True.
Proof. exact (TRANS (@lem5782334 A B x s P f h1) (@lem5782338 A)). Qed.
Lemma lem5782340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782341 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) (h1 : term315 A B x s P f) : (term369 A B s P f) = (and True).
Proof. exact (MK_COMB (@lem5782340) (@lem5782339 A B x s P f h1)). Qed.
Lemma lem5782353 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term89 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem5782354 (p : Prop) (q : Prop) (p' : Prop) : term90 p q p'.
Proof. exact (fun q' : Prop => @lem5782353 p q p' q'). Qed.
Lemma lem5782355 (p : Prop) (q : Prop) : term91 p q.
Proof. exact (fun p' : Prop => @lem5782354 p q p'). Qed.
Lemma lem5782356 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) : term370 B P op x y.
Proof. exact (@lem5782355 (term293 B x P y) (term294 B P op x y)). Qed.
Lemma lem5782357 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) (p' : Prop) : term371 B P op x y p'.
Proof. exact (@lem5782356 B P op x y p'). Qed.
Lemma lem5782358 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) (p' : Prop) : (term371 B P op x y p') = (term372 B P op x y p').
Proof. exact (eq_refl (term371 B P op x y p')). Qed.
Lemma lem5782359 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) (p' : Prop) : term372 B P op x y p'.
Proof. exact (EQ_MP (@lem5782358 B P op x y p') (@lem5782357 B P op x y p')). Qed.
Lemma lem5782360 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) (p' : Prop) (q' : Prop) : term373 B P op x y p' q'.
Proof. exact (@lem5782359 B P op x y p' q'). Qed.
Lemma lem5782361 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) (p' : Prop) (q' : Prop) : (term373 B P op x y p' q') = (term374 B P op x y p' q').
Proof. exact (eq_refl (term373 B P op x y p' q')). Qed.
Lemma lem5782362 {B : Type'} (P : B -> Prop) (op : type1400 B) (x : B) (y : B) (p' : Prop) (q' : Prop) : term374 B P op x y p' q'.
Proof. exact (EQ_MP (@lem5782361 B P op x y p' q') (@lem5782360 B P op x y p' q')). Qed.
Lemma lem5782365 {B : Type'} (x : B) (P : B -> Prop) (y : B) : (term293 B x P y) = (term293 B x P y).
Proof. exact (eq_refl (term293 B x P y)). Qed.
Lemma lem5782366 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (q' : Prop) : term375 B op x P y q'.
Proof. exact (@lem5782362 B P op x y (term293 B x P y) q'). Qed.
Lemma lem5782367 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (q' : Prop) : term376 B op x P y q'.
Proof. exact (@lem5782366 B op x P y q' (@lem5782365 B x P y)). Qed.
Lemma lem5782368 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : term293 B x P y.
Proof. exact (h1). Qed.
Lemma lem5782369 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : P y.
Proof. exact (proj2 (@lem5782368 B x P y h1)). Qed.
Lemma lem5782370 {B : Type'} (P : B -> Prop) (y : B) : (P y) = ((P y) = True).
Proof. exact (@lem7 (P y)). Qed.
Lemma lem5782372 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : P x.
Proof. exact (proj1 (@lem5782368 B x P y h1)). Qed.
Lemma lem5782373 {B : Type'} (P : B -> Prop) (x : B) : (P x) = ((P x) = True).
Proof. exact (@lem7 (P x)). Qed.
Lemma lem5782376 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term345 B P op x y.
Proof. exact (fun h0 : term293 B x P y => @lem5781962 B op x P y h1 h0). Qed.
Lemma lem5782377 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term345 B P op x y.
Proof. exact (@lem5782376 B x y P op h1). Qed.
Lemma lem5782381 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : (P x) = True.
Proof. exact (EQ_MP (@lem5782373 B P x) (@lem5782372 B x P y h1)). Qed.
Lemma lem5782382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782383 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : (term377 B P x) = (and True).
Proof. exact (MK_COMB (@lem5782382) (@lem5782381 B x P y h1)). Qed.
Lemma lem5782385 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : (P y) = True.
Proof. exact (EQ_MP (@lem5782370 B P y) (@lem5782369 B x P y h1)). Qed.
Lemma lem5782386 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : (term293 B x P y) = (True /\ True).
Proof. exact (MK_COMB (@lem5782383 B x P y h1) (@lem5782385 B x P y h1)). Qed.
Lemma lem5782388 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782389 : (True /\ True) = True.
Proof. exact (@lem5782388 True). Qed.
Lemma lem5782390 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : (term293 B x P y) = True.
Proof. exact (TRANS (@lem5782386 B x P y h1) (@lem5782389)). Qed.
Lemma lem5782391 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : True = (term293 B x P y).
Proof. exact (SYM (@lem5782390 B x P y h1)). Qed.
Lemma lem5782392 {B : Type'} (x : B) (P : B -> Prop) (y : B) (h1 : term293 B x P y) : term293 B x P y.
Proof. exact (EQ_MP (@lem5782391 B x P y h1) (@lem0)). Qed.
Lemma lem5782393 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) (h1 : term36 B P op) (h2 : term293 B x P y) : (term294 B P op x y) = True.
Proof. exact (@lem5782377 B x y P op h1 (@lem5782392 B x P y h2)). Qed.
Lemma lem5782394 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : term345 B P op x y.
Proof. exact (fun h0 : term293 B x P y => @lem5782393 B op x P y h1 h0). Qed.
Lemma lem5782395 {B : Type'} (op : type1400 B) (x : B) (P : B -> Prop) (y : B) : term378 B op x P y.
Proof. exact (@lem5782367 B op x P y True). Qed.
Lemma lem5782396 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term292 B P op x y) = (term379 B x P y).
Proof. exact (@lem5782395 B op x P y (@lem5782394 B x y P op h1)). Qed.
Lemma lem5782398 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782399 {B : Type'} (x : B) (P : B -> Prop) (y : B) : (term379 B x P y) = True.
Proof. exact (@lem5782398 (term293 B x P y)). Qed.
Lemma lem5782400 {B : Type'} (x : B) (y : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term292 B P op x y) = True.
Proof. exact (TRANS (@lem5782396 B x y P op h1) (@lem5782399 B x P y)). Qed.
Lemma lem5782401 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term380 B P op x) = (term366 B).
Proof. exact (fun_ext (fun y : B => @lem5782400 B x y P op h1)). Qed.
Lemma lem5782402 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5782403 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term290 B P op x) = (term367 B).
Proof. exact (MK_COMB (@lem5782402 B) (@lem5782401 B x P op h1)). Qed.
Lemma lem5782405 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5782406 {B : Type'} (t : Prop) : (term368 B t) = t.
Proof. exact (@lem5782405 B t). Qed.
Lemma lem5782407 {B : Type'} : (term367 B) = True.
Proof. exact (@lem5782406 B True). Qed.
Lemma lem5782408 {B : Type'} (x : B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term290 B P op x) = True.
Proof. exact (TRANS (@lem5782403 B x P op h1) (@lem5782407 B)). Qed.
Lemma lem5782409 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term381 B P op) = (term366 B).
Proof. exact (fun_ext (fun x : B => @lem5782408 B x P op h1)). Qed.
Lemma lem5782410 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5782411 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term36 B P op) = (term367 B).
Proof. exact (MK_COMB (@lem5782410 B) (@lem5782409 B P op h1)). Qed.
Lemma lem5782413 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5782414 {B : Type'} (t : Prop) : (term368 B t) = t.
Proof. exact (@lem5782413 B t). Qed.
Lemma lem5782415 {B : Type'} : (term367 B) = True.
Proof. exact (@lem5782414 B True). Qed.
Lemma lem5782416 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) : (term36 B P op) = True.
Proof. exact (TRANS (@lem5782411 B P op h1) (@lem5782415 B)). Qed.
Lemma lem5782417 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) : (term262 A B s f P op) = (True /\ True).
Proof. exact (MK_COMB (@lem5782341 A B x s P f h1) (@lem5782416 B P op h2)). Qed.
Lemma lem5782419 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782420 : (True /\ True) = True.
Proof. exact (@lem5782419 True). Qed.
Lemma lem5782421 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) : (term262 A B s f P op) = True.
Proof. exact (TRANS (@lem5782417 A B x s f P op h1 h2) (@lem5782420)). Qed.
Lemma lem5782422 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782423 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) : (term382 A B s f P op) = (and True).
Proof. exact (MK_COMB (@lem5782422) (@lem5782421 A B x s f P op h1 h2)). Qed.
Lemma lem5782425 {B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = True.
Proof. exact (EQ_MP (@lem5781876 B op) (@lem5781875 B op h1)). Qed.
Lemma lem5782426 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) : (term264 A B s f P op) = (True /\ True).
Proof. exact (MK_COMB (@lem5782423 A B x s f P op h1 h2) (@lem5782425 B op h3)). Qed.
Lemma lem5782428 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782429 : (True /\ True) = True.
Proof. exact (@lem5782428 True). Qed.
Lemma lem5782430 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) : (term264 A B s f P op) = True.
Proof. exact (TRANS (@lem5782426 A B x s f P op h1 h2 h3) (@lem5782429)). Qed.
Lemma lem5782431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5782432 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) : (term383 A B s f P op) = (and True).
Proof. exact (MK_COMB (@lem5782431) (@lem5782430 A B x s f P op h1 h2 h3)). Qed.
Lemma lem5782434 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term37 B P op) : (term37 B P op) = True.
Proof. exact (EQ_MP (@lem5781895 B P op) (@lem5781894 B P op h1)). Qed.
Lemma lem5782435 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : (term384 A B s f P op) = (True /\ True).
Proof. exact (MK_COMB (@lem5782432 A B x s f P op h1 h2 h3) (@lem5782434 B P op h4)). Qed.
Lemma lem5782437 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782438 : (True /\ True) = True.
Proof. exact (@lem5782437 True). Qed.
Lemma lem5782439 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : (term384 A B s f P op) = True.
Proof. exact (TRANS (@lem5782435 A B x s f P op h1 h2 h3 h4) (@lem5782438)). Qed.
Lemma lem5782440 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : True = (term384 A B s f P op).
Proof. exact (SYM (@lem5782439 A B x s f P op h1 h2 h3 h4)). Qed.
Lemma lem5782441 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : term384 A B s f P op.
Proof. exact (EQ_MP (@lem5782440 A B x s f P op h1 h2 h3 h4) (@lem0)). Qed.
Lemma lem5782442 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : (term40 A B P op s f) = True.
Proof. exact (@lem5782223 A B P op f x s h5 (@lem5782441 A B x s f P op h1 h2 h3 h4)). Qed.
Lemma lem5782443 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : (term385 A B x P op s f) = (True /\ True).
Proof. exact (MK_COMB (@lem5782221 A B P op f x s h1 h5) (@lem5782442 A B P op f x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5782445 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782446 : (True /\ True) = True.
Proof. exact (@lem5782445 True). Qed.
Lemma lem5782447 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : (term385 A B x P op s f) = True.
Proof. exact (TRANS (@lem5782443 A B P op f x s h1 h2 h3 h4 h5) (@lem5782446)). Qed.
Lemma lem5782448 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : True = (term385 A B x P op s f).
Proof. exact (SYM (@lem5782447 A B P op f x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5782449 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : term385 A B x P op s f.
Proof. exact (EQ_MP (@lem5782448 A B P op f x s h1 h2 h3 h4 h5) (@lem0)). Qed.
Lemma lem5782450 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : (term344 A B P x op s f) = True.
Proof. exact (@lem5782196 A B x s f P op h2 (@lem5782449 A B P op f x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5782451 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term315 A B x s P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) (h5 : term147 A B P op f x s) : (term297 A B P op x s f) = True.
Proof. exact (TRANS (@lem5782192 A B P op f x s h3 h5) (@lem5782450 A B P op f x s h1 h2 h3 h4 h5)). Qed.
Lemma lem5782452 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) (h4 : term147 A B P op f x s) : term386 A B P op x s f.
Proof. exact (fun h0 : term315 A B x s P f => @lem5782451 A B P op f x s h0 h1 h2 h3 h4). Qed.
Lemma lem5782453 {A B : Type'} (op : type1400 B) (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : term387 A B op x s P f.
Proof. exact (@lem5782116 A B op x s P f True). Qed.
Lemma lem5782454 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) (h4 : term147 A B P op f x s) : (term282 A B P op x s f) = (term388 A B x s P f).
Proof. exact (@lem5782453 A B op x s P f (@lem5782452 A B P op f x s h1 h2 h3 h4)). Qed.
Lemma lem5782456 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782457 {A B : Type'} (x : A) (s : A -> Prop) (P : B -> Prop) (f : A -> B) : (term388 A B x s P f) = True.
Proof. exact (@lem5782456 (term315 A B x s P f)). Qed.
Lemma lem5782458 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) (h4 : term147 A B P op f x s) : (term282 A B P op x s f) = True.
Proof. exact (TRANS (@lem5782454 A B P op f x s h1 h2 h3 h4) (@lem5782457 A B x s P f)). Qed.
Lemma lem5782459 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term37 B P op) (h3 : term147 A B P op f x s) : term389 A B P op x s f.
Proof. exact (fun h0 : term36 B P op => @lem5782458 A B P op f x s h0 h1 h2 h3). Qed.
Lemma lem5782460 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term390 A B x s f P op.
Proof. exact (@lem5781951 A B x s f P op True). Qed.
Lemma lem5782461 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term37 B P op) (h3 : term147 A B P op f x s) : (term274 A B P op x s f) = (term128 B P op).
Proof. exact (@lem5782460 A B x s f P op (@lem5782459 A B P op f x s h1 h2 h3)). Qed.
Lemma lem5782463 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782464 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term128 B P op) = True.
Proof. exact (@lem5782463 (term36 B P op)). Qed.
Lemma lem5782465 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term37 B P op) (h3 : term147 A B P op f x s) : (term274 A B P op x s f) = True.
Proof. exact (TRANS (@lem5782461 A B P op f x s h1 h2 h3) (@lem5782464 B P op)). Qed.
Lemma lem5782466 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : term391 A B P op x s f.
Proof. exact (fun h0 : term37 B P op => @lem5782465 A B P op f x s h1 h0 h2). Qed.
Lemma lem5782467 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term392 A B x s f P op.
Proof. exact (@lem5781893 A B x s f P op True). Qed.
Lemma lem5782468 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term266 A B P op x s f) = (term131 B P op).
Proof. exact (@lem5782467 A B x s f P op (@lem5782466 A B P op f x s h1 h2)). Qed.
Lemma lem5782470 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782471 {B : Type'} (P : B -> Prop) (op : type1400 B) : (term131 B P op) = True.
Proof. exact (@lem5782470 (term37 B P op)). Qed.
Lemma lem5782472 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : @monoidal B op) (h2 : term147 A B P op f x s) : (term266 A B P op x s f) = True.
Proof. exact (TRANS (@lem5782468 A B P op f x s h1 h2) (@lem5782471 B P op)). Qed.
Lemma lem5782473 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : term393 A B P op x s f.
Proof. exact (fun h0 : @monoidal B op => @lem5782472 A B P op f x s h0 h1). Qed.
Lemma lem5782474 {A B : Type'} (P : B -> Prop) (x : A) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term394 A B P x s f op.
Proof. exact (@lem5781874 A B P x s f op True). Qed.
Lemma lem5782475 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term151 A B P op x s f) = (term134 B op).
Proof. exact (@lem5782474 A B P x s f op (@lem5782473 A B P op f x s h1)). Qed.
Lemma lem5782477 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782478 {B : Type'} (op : type1400 B) : (term134 B op) = True.
Proof. exact (@lem5782477 (@monoidal B op)). Qed.
Lemma lem5782479 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) (h1 : term147 A B P op f x s) : (term151 A B P op x s f) = True.
Proof. exact (TRANS (@lem5782475 A B P op f x s h1) (@lem5782478 B op)). Qed.
Lemma lem5782480 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : term395 A B P op x s f.
Proof. exact (fun h0 : term147 A B P op f x s => @lem5782479 A B P op f x s h0). Qed.
Lemma lem5782481 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : term396 A B P op f x s.
Proof. exact (@lem5781819 A B P op f x s True). Qed.
Lemma lem5782482 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term153 A B P op x s f) = (term397 A B P op f x s).
Proof. exact (@lem5782481 A B P op f x s (@lem5782480 A B P op x s f)). Qed.
Lemma lem5782484 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem5782485 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (x : A) (s : A -> Prop) : (term397 A B P op f x s) = True.
Proof. exact (@lem5782484 (term147 A B P op f x s)). Qed.
Lemma lem5782486 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (s : A -> Prop) (f : A -> B) : (term153 A B P op x s f) = True.
Proof. exact (TRANS (@lem5782482 A B P op f x s) (@lem5782485 A B P op f x s)). Qed.
Lemma lem5782487 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term155 A B P op x f) = (term398 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5782486 A B P op x s f)). Qed.
Lemma lem5782488 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5782489 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term157 A B P op x f) = (term399 A).
Proof. exact (MK_COMB (@lem5782488 A) (@lem5782487 A B P op x f)). Qed.
Lemma lem5782491 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5782492 {A : Type'} (t : Prop) : (term400 A t) = t.
Proof. exact (@lem5782491 (A -> Prop) t). Qed.
Lemma lem5782493 {A : Type'} : (term399 A) = True.
Proof. exact (@lem5782492 A True). Qed.
Lemma lem5782494 {A B : Type'} (P : B -> Prop) (op : type1400 B) (x : A) (f : A -> B) : (term157 A B P op x f) = True.
Proof. exact (TRANS (@lem5782489 A B P op x f) (@lem5782493 A)). Qed.
Lemma lem5782495 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term159 A B P op f) = (term366 A).
Proof. exact (fun_ext (fun x : A => @lem5782494 A B P op x f)). Qed.
Lemma lem5782496 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5782497 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term161 A B P op f) = (term367 A).
Proof. exact (MK_COMB (@lem5782496 A) (@lem5782495 A B P op f)). Qed.
Lemma lem5782499 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5782500 {A : Type'} (t : Prop) : (term368 A t) = t.
Proof. exact (@lem5782499 A t). Qed.
Lemma lem5782501 {A : Type'} : (term367 A) = True.
Proof. exact (@lem5782500 A True). Qed.
Lemma lem5782502 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term161 A B P op f) = True.
Proof. exact (TRANS (@lem5782497 A B P op f) (@lem5782501 A)). Qed.
Lemma lem5782503 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term163 A B P op f) = (True /\ True).
Proof. exact (MK_COMB (@lem5780570 A B P op f) (@lem5782502 A B P op f)). Qed.
Lemma lem5782505 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5782506 : (True /\ True) = True.
Proof. exact (@lem5782505 True). Qed.
Lemma lem5782507 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : (term163 A B P op f) = True.
Proof. exact (TRANS (@lem5782503 A B P op f) (@lem5782506)). Qed.
Lemma lem5782508 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : True = (term163 A B P op f).
Proof. exact (SYM (@lem5782507 A B P op f)). Qed.
Lemma lem5782509 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term163 A B P op f.
Proof. exact (EQ_MP (@lem5782508 A B P op f) (@lem0)). Qed.
Lemma lem5782510 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) : term172 A B P op f.
Proof. exact (@lem5780309 A B P op f (@lem5782509 A B P op f)). Qed.
Lemma lem5782511 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) : term401 A B P op f s.
Proof. exact (@lem5782510 A B P op f (@support A B op f s)). Qed.
Lemma lem5782512 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : (term401 A B P op f s) = (term83 A B P op s f).
Proof. exact (eq_refl (term401 A B P op f s)). Qed.
Lemma lem5782513 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term83 A B P op s f.
Proof. exact (EQ_MP (@lem5782512 A B P op s f) (@lem5782511 A B P op f s)). Qed.
Lemma lem5782516 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term75 A B s f P op.
Proof. exact (EQ_MP (@lem5780275 A B s f P op) (@lem0)). Qed.
Lemma lem5782517 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term78 A B s f P op.
Proof. exact (fun h0 : term402 A B op f s => @lem5782516 A B s f P op). Qed.
Lemma lem5782518 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term73 A B op f s) : term80 A B P op s f.
Proof. exact (@lem5782513 A B P op s f (@lem5778819 A B op f s h1)). Qed.
Lemma lem5782519 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term73 A B op f s) : (term73 A B op f s) = (term80 A B P op s f).
Proof. exact (prop_ext (fun h2 : term73 A B op f s => @lem5782518 A B P op f s h1) (fun h2 : term80 A B P op s f => @lem5778819 A B op f s h1)). Qed.
Lemma lem5782520 {A B : Type'} (P : B -> Prop) (op : type1400 B) (f : A -> B) (s : A -> Prop) (h1 : term73 A B op f s) : term80 A B P op s f.
Proof. exact (EQ_MP (@lem5782519 A B P op f s h1) (@lem5778819 A B op f s h1)). Qed.
Lemma lem5782521 {A B : Type'} (P : B -> Prop) (op : type1400 B) (s : A -> Prop) (f : A -> B) : term83 A B P op s f.
Proof. exact (fun h0 : term73 A B op f s => @lem5782520 A B P op f s h0). Qed.
Lemma lem5782522 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) : term86 A B s f P op.
Proof. exact (conj (@lem5782521 A B P op s f) (@lem5782517 A B s f P op)). Qed.
Lemma lem5782523 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term64 A B P s f op.
Proof. exact (EQ_MP (@lem5778818 A B P s f op) (@lem5782522 A B s f P op)). Qed.
Lemma lem5782524 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) : term63 A B P s f op.
Proof. exact (EQ_MP (@lem5778800 A B P s f op) (@lem5782523 A B P s f op)). Qed.
Lemma lem5782525 {A B : Type'} (P : B -> Prop) (s : A -> Prop) (f : A -> B) (op : type1400 B) (h1 : @monoidal B op) : term60 A B P s f op.
Proof. exact (@lem5782524 A B P s f op (@lem5778729 B op h1)). Qed.
Lemma lem5782526 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) : term57 A B P s f op.
Proof. exact (@lem5782525 A B P s f op h1 (@lem5778732 B P op h2)). Qed.
Lemma lem5782527 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : term54 A B P s f op.
Proof. exact (@lem5782526 A B s f P op h2 h3 (@lem5778731 B P op h1)). Qed.
Lemma lem5782528 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term38 A B s op P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : term41 A B P s f op.
Proof. exact (@lem5782527 A B s f P op h2 h3 h4 (@lem5778733 A B s op P f h1)). Qed.
Lemma lem5782529 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term38 A B s op P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : term40 A B P op s f.
Proof. exact (EQ_MP (@lem5778739 A B P op s f) (@lem5782528 A B s f P op h1 h2 h3 h4)). Qed.
Lemma lem5782530 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term38 A B s op P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : (term38 A B s op P f) = (term40 A B P op s f).
Proof. exact (prop_ext (fun h5 : term38 A B s op P f => @lem5782529 A B s f P op h1 h2 h3 h4) (fun h5 : term40 A B P op s f => @lem5778733 A B s op P f h1)). Qed.
Lemma lem5782531 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term38 A B s op P f) (h2 : term36 B P op) (h3 : @monoidal B op) (h4 : term37 B P op) : term40 A B P op s f.
Proof. exact (EQ_MP (@lem5782530 A B s f P op h1 h2 h3 h4) (@lem5778733 A B s op P f h1)). Qed.
Lemma lem5782532 {A B : Type'} (s : A -> Prop) (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : term403 A B P op s f.
Proof. exact (fun h0 : term38 A B s op P f => @lem5782531 A B s f P op h0 h1 h2 h3). Qed.
Lemma lem5782537 {A B : Type'} (f : A -> B) (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : term404 A B P op f.
Proof. exact (fun s : A -> Prop => @lem5782532 A B s f P op h1 h2 h3). Qed.
Lemma lem5782542 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : term405 A B P op.
Proof. exact (fun f : A -> B => @lem5782537 A B f P op h1 h2 h3). Qed.
Lemma lem5782543 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term35 B P op) : term36 B P op.
Proof. exact (proj2 (@lem5778730 B P op h1)). Qed.
Lemma lem5782544 {B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term35 B P op) : term37 B P op.
Proof. exact (proj1 (@lem5778730 B P op h1)). Qed.
Lemma lem5782545 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : (term36 B P op) = (term405 A B P op).
Proof. exact (prop_ext (fun h4 : term36 B P op => @lem5782542 A B P op h1 h2 h3) (fun h4 : term405 A B P op => @lem5778731 B P op h1)). Qed.
Lemma lem5782546 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : term405 A B P op.
Proof. exact (EQ_MP (@lem5782545 A B P op h1 h2 h3) (@lem5778731 B P op h1)). Qed.
Lemma lem5782547 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : (term37 B P op) = (term405 A B P op).
Proof. exact (prop_ext (fun h4 : term37 B P op => @lem5782546 A B P op h1 h2 h3) (fun h4 : term405 A B P op => @lem5778732 B P op h3)). Qed.
Lemma lem5782548 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : term36 B P op) (h2 : @monoidal B op) (h3 : term37 B P op) : term405 A B P op.
Proof. exact (EQ_MP (@lem5782547 A B P op h1 h2 h3) (@lem5778732 B P op h3)). Qed.
Lemma lem5782549 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) (h3 : term35 B P op) : (term36 B P op) = (term405 A B P op).
Proof. exact (prop_ext (fun h4 : term36 B P op => @lem5782548 A B P op h4 h1 h2) (fun h4 : term405 A B P op => @lem5782543 B P op h3)). Qed.
Lemma lem5782550 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term37 B P op) (h3 : term35 B P op) : term405 A B P op.
Proof. exact (EQ_MP (@lem5782549 A B P op h1 h2 h3) (@lem5782543 B P op h3)). Qed.
Lemma lem5782551 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term35 B P op) : (term37 B P op) = (term405 A B P op).
Proof. exact (prop_ext (fun h3 : term37 B P op => @lem5782550 A B P op h1 h3 h2) (fun h3 : term405 A B P op => @lem5782544 B P op h2)). Qed.
Lemma lem5782552 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) (h2 : term35 B P op) : term405 A B P op.
Proof. exact (EQ_MP (@lem5782551 A B P op h1 h2) (@lem5782544 B P op h2)). Qed.
Lemma lem5782553 {A B : Type'} (P : B -> Prop) (op : type1400 B) (h1 : @monoidal B op) : term406 A B P op.
Proof. exact (fun h0 : term35 B P op => @lem5782552 A B P op h1 h0). Qed.
Lemma lem5782558 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term407 A B op.
Proof. exact (fun P : B -> Prop => @lem5782553 A B P op h1). Qed.
Lemma lem5782559 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : (@monoidal B op) = (term407 A B op).
Proof. exact (prop_ext (fun h2 : @monoidal B op => @lem5782558 A B op h1) (fun h2 : term407 A B op => @lem5778729 B op h1)). Qed.
Lemma lem5782560 {A B : Type'} (op : type1400 B) (h1 : @monoidal B op) : term407 A B op.
Proof. exact (EQ_MP (@lem5782559 A B op h1) (@lem5778729 B op h1)). Qed.
Lemma lem5782561 {A B : Type'} (op : type1400 B) : term408 A B op.
Proof. exact (fun h0 : @monoidal B op => @lem5782560 A B op h0). Qed.
Lemma lem5782566 {A B : Type'} : term409 A B.
Proof. exact (fun op : type1400 B => @lem5782561 A B op). Qed.
