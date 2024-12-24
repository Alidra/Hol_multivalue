Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_SWAP_term_abbrevs.
Require Import ETA_AX_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUM_0_spec.
Require Import SUM_ADD_spec.
Require Import SUM_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Require Import thm885_spec.
Require Import thm886_spec.
Lemma lem7123776 {A B : Type'} (t : A -> B) : term0 A B t.
Proof. exact (@lem9121 A B t). Qed.
Lemma lem7123777 {A B : Type'} (t : A -> B) : (term0 A B t) = ((term1 A B t) = t).
Proof. exact (eq_refl (term0 A B t)). Qed.
Lemma lem7123778 {A B : Type'} (t : A -> B) : (term1 A B t) = t.
Proof. exact (EQ_MP (@lem7123777 A B t) (@lem7123776 A B t)). Qed.
Lemma lem7123779 {_131713 : Type'} (f : _131713 -> real) : term2 _131713 f.
Proof. exact (@lem7068796 _131713 f). Qed.
Lemma lem7123780 {_131713 : Type'} (f : _131713 -> real) : (term2 _131713 f) = (term3 _131713 f).
Proof. exact (eq_refl (term2 _131713 f)). Qed.
Lemma lem7123781 {_131713 : Type'} (f : _131713 -> real) : term3 _131713 f.
Proof. exact (EQ_MP (@lem7123780 _131713 f) (@lem7123779 _131713 f)). Qed.
Lemma lem7123782 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : term4 _131713 f g.
Proof. exact (@lem7123781 _131713 f g). Qed.
Lemma lem7123783 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : (term4 _131713 f g) = (term5 _131713 f g).
Proof. exact (eq_refl (term4 _131713 f g)). Qed.
Lemma lem7123784 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) : term5 _131713 f g.
Proof. exact (EQ_MP (@lem7123783 _131713 f g) (@lem7123782 _131713 f g)). Qed.
Lemma lem7123785 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) : term6 _131713 f g s.
Proof. exact (@lem7123784 _131713 f g s). Qed.
Lemma lem7123786 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : (term6 _131713 f g s) = (term7 _131713 f s g).
Proof. exact (eq_refl (term6 _131713 f g s)). Qed.
Lemma lem7123787 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term7 _131713 f s g.
Proof. exact (EQ_MP (@lem7123786 _131713 f s g) (@lem7123785 _131713 f g s)). Qed.
Lemma lem7123788 {_131713 : Type'} (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : @FINITE _131713 s.
Proof. exact (h1). Qed.
Lemma lem7123789 {_131713 : Type'} (f : _131713 -> real) (g : _131713 -> real) (s : _131713 -> Prop) (h1 : @FINITE _131713 s) : (term8 _131713 s f g) = (term9 _131713 f s g).
Proof. exact (@lem7123787 _131713 f s g (@lem7123788 _131713 s h1)). Qed.
Lemma lem7123795 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem7069399 A s). Qed.
Lemma lem7123796 {A : Type'} (s : A -> Prop) : (term10 A s) = ((term11 A s) = term12).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem7123798 {_131524 : Type'} : term13 _131524.
Proof. exact (proj2 (@lem7067645 Prop _131524)). Qed.
Lemma lem7123799 {_131524 : Type'} (x : _131524) : term14 _131524 x.
Proof. exact (@lem7123798 _131524 x). Qed.
Lemma lem7123800 {_131524 : Type'} (x : _131524) : (term14 _131524 x) = (term15 _131524 x).
Proof. exact (eq_refl (term14 _131524 x)). Qed.
Lemma lem7123801 {_131524 : Type'} (x : _131524) : term15 _131524 x.
Proof. exact (EQ_MP (@lem7123800 _131524 x) (@lem7123799 _131524 x)). Qed.
Lemma lem7123802 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term16 _131524 x f.
Proof. exact (@lem7123801 _131524 x f). Qed.
Lemma lem7123803 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : (term16 _131524 x f) = (term17 _131524 x f).
Proof. exact (eq_refl (term16 _131524 x f)). Qed.
Lemma lem7123804 {_131524 : Type'} (x : _131524) (f : _131524 -> real) : term17 _131524 x f.
Proof. exact (EQ_MP (@lem7123803 _131524 x f) (@lem7123802 _131524 x f)). Qed.
Lemma lem7123805 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) : term18 _131524 x f s.
Proof. exact (@lem7123804 _131524 x f s). Qed.
Lemma lem7123806 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : (term18 _131524 x f s) = (term19 _131524 x s f).
Proof. exact (eq_refl (term18 _131524 x f s)). Qed.
Lemma lem7123807 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term19 _131524 x s f.
Proof. exact (EQ_MP (@lem7123806 _131524 x s f) (@lem7123805 _131524 x f s)). Qed.
Lemma lem7123808 {_131524 : Type'} (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : @FINITE _131524 s.
Proof. exact (h1). Qed.
Lemma lem7123809 {_131524 : Type'} (x : _131524) (f : _131524 -> real) (s : _131524 -> Prop) (h1 : @FINITE _131524 s) : (term20 _131524 x s f) = (term21 _131524 x s f).
Proof. exact (@lem7123807 _131524 x s f (@lem7123808 _131524 s h1)). Qed.
Lemma lem7123815 {_131483 : Type'} : term22 _131483.
Proof. exact (proj1 (@lem7067645 _131483 Prop)). Qed.
Lemma lem7123816 {_131483 : Type'} (f : _131483 -> real) : term23 _131483 f.
Proof. exact (@lem7123815 _131483 f). Qed.
Lemma lem7123817 {_131483 : Type'} (f : _131483 -> real) : (term23 _131483 f) = ((@sum _131483 (@EMPTY _131483) f) = term12).
Proof. exact (eq_refl (term23 _131483 f)). Qed.
Lemma lem7123819 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem7123820 {A : Type'} (P : type686 A) (h1 : term24 A) : term25 A P.
Proof. exact (@lem7123819 A h1 P). Qed.
Lemma lem7123821 {A : Type'} (P : type686 A) : (term25 A P) = (term26 A P).
Proof. exact (eq_refl (term25 A P)). Qed.
Lemma lem7123822 {A : Type'} (P : type686 A) (h1 : term24 A) : term26 A P.
Proof. exact (EQ_MP (@lem7123821 A P) (@lem7123820 A P h1)). Qed.
Lemma lem7123823 {A : Type'} (P : type686 A) (h1 : term27 A P) : term27 A P.
Proof. exact (h1). Qed.
Lemma lem7123824 {A : Type'} (P : type686 A) (h1 : term24 A) (h2 : term27 A P) : term28 A P.
Proof. exact (@lem7123822 A P h1 (@lem7123823 A P h2)). Qed.
Lemma lem7123825 {A : Type'} (P : type686 A) (h1 : term27 A P) : term29 A P.
Proof. exact (fun h0 : term24 A => @lem7123824 A P h0 h1). Qed.
Lemma lem7123826 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (h1). Qed.
Lemma lem7123827 {A : Type'} (P : type686 A) (h1 : term24 A) (h2 : term27 A P) : term28 A P.
Proof. exact (@lem7123825 A P h2 (@lem7123826 A h1)). Qed.
Lemma lem7123828 {A : Type'} (P : type686 A) (h1 : term24 A) : term26 A P.
Proof. exact (fun h0 : term27 A P => @lem7123827 A P h1 h0). Qed.
Lemma lem7123829 {A : Type'} (h1 : term24 A) : term24 A.
Proof. exact (fun P : type686 A => @lem7123828 A P h1). Qed.
Lemma lem7123830 {A : Type'} : term30 A.
Proof. exact (fun h0 : term24 A => @lem7123829 A h0). Qed.
Lemma lem7123831 {A : Type'} : term24 A.
Proof. exact (@lem7123830 A (@lem3558722 A)). Qed.
Lemma lem7123832 {A : Type'} (P : type686 A) : term25 A P.
Proof. exact (@lem7123831 A P). Qed.
Lemma lem7123833 {A : Type'} (P : type686 A) : (term25 A P) = (term26 A P).
Proof. exact (eq_refl (term25 A P)). Qed.
Lemma lem7123835 {A : Type'} (P : Prop) : term31 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem7123836 {A : Type'} (P : Prop) : (term31 A P) = (term32 A P).
Proof. exact (eq_refl (term31 A P)). Qed.
Lemma lem7123837 {A : Type'} (P : Prop) : term32 A P.
Proof. exact (EQ_MP (@lem7123836 A P) (@lem7123835 A P)). Qed.
Lemma lem7123838 {A : Type'} (P : Prop) (Q : A -> Prop) : term33 A P Q.
Proof. exact (@lem7123837 A P Q). Qed.
Lemma lem7123839 {A : Type'} (P : Prop) (Q : A -> Prop) : (term33 A P Q) = ((term34 A P Q) = (term35 A P Q)).
Proof. exact (eq_refl (term33 A P Q)). Qed.
Lemma lem7123870 (p : Prop) (q : Prop) (r : Prop) : (term36 p q r) = (term37 p q r).
Proof. exact (EQ_MP (@lem886 p q r) (@lem885 p q r)). Qed.
Lemma lem7123871 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term38 A B t s f) = (term39 A B t s f).
Proof. exact (@lem7123870 (@FINITE A s) (@FINITE B t) ((term40 A B s t f) = (term41 A B t s f))). Qed.
Lemma lem7123878 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term42 A B s f) = (term43 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7123871 A B t s f)). Qed.
Lemma lem7123879 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7123880 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term44 A B s f) = (term45 A B s f).
Proof. exact (MK_COMB (@lem7123879 B) (@lem7123878 A B s f)). Qed.
Lemma lem7123882 {A : Type'} (P : Prop) (Q : A -> Prop) : (term34 A P Q) = (term35 A P Q).
Proof. exact (EQ_MP (@lem7123839 A P Q) (@lem7123838 A P Q)). Qed.
Lemma lem7123883 {B : Type'} (P : Prop) (Q : type686 B) : (term46 B P Q) = (term47 B P Q).
Proof. exact (@lem7123882 (B -> Prop) P Q). Qed.
Lemma lem7123884 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term48 A B s f) = (term49 A B s f).
Proof. exact (@lem7123883 B (@FINITE A s) (term50 A B s f)). Qed.
Lemma lem7123885 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term51 A B s f t) = (term52 A B t s f).
Proof. exact (eq_refl (term51 A B s f t)). Qed.
Lemma lem7123886 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem7123887 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term54 A B s f t) = (term39 A B t s f).
Proof. exact (MK_COMB (@lem7123886 A s) (@lem7123885 A B t s f)). Qed.
Lemma lem7123888 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term55 A B s f) = (term43 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7123887 A B t s f)). Qed.
Lemma lem7123889 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7123890 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term48 A B s f) = (term45 A B s f).
Proof. exact (MK_COMB (@lem7123889 B) (@lem7123888 A B s f)). Qed.
Lemma lem7123891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7123892 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term56 A B s f) = (term57 A B s f).
Proof. exact (MK_COMB (@lem7123891) (@lem7123890 A B s f)). Qed.
Lemma lem7123893 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term51 A B s f t) = (term52 A B t s f).
Proof. exact (eq_refl (term51 A B s f t)). Qed.
Lemma lem7123894 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term58 A B s f) = (term50 A B s f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7123893 A B t s f)). Qed.
Lemma lem7123895 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7123896 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term59 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem7123895 B) (@lem7123894 A B s f)). Qed.
Lemma lem7123897 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem7123898 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term49 A B s f) = (term61 A B s f).
Proof. exact (MK_COMB (@lem7123897 A s) (@lem7123896 A B s f)). Qed.
Lemma lem7123899 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : ((term48 A B s f) = (term49 A B s f)) = ((term45 A B s f) = (term61 A B s f)).
Proof. exact (MK_COMB (@lem7123892 A B s f) (@lem7123898 A B s f)). Qed.
Lemma lem7123900 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term45 A B s f) = (term61 A B s f).
Proof. exact (EQ_MP (@lem7123899 A B s f) (@lem7123884 A B s f)). Qed.
Lemma lem7123931 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term44 A B s f) = (term61 A B s f).
Proof. exact (TRANS (@lem7123880 A B s f) (@lem7123900 A B s f)). Qed.
Lemma lem7123932 {A B : Type'} (f : type1416 A B) : (term62 A B f) = (term63 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7123931 A B s f)). Qed.
Lemma lem7123933 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7123934 {A B : Type'} (f : type1416 A B) : (term64 A B f) = (term65 A B f).
Proof. exact (MK_COMB (@lem7123933 A) (@lem7123932 A B f)). Qed.
Lemma lem7123959 {A B : Type'} (f : type1416 A B) : (term65 A B f) = (term64 A B f).
Proof. exact (SYM (@lem7123934 A B f)). Qed.
Lemma lem7123961 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (EQ_MP (@lem7123833 A P) (@lem7123832 A P)). Qed.
Lemma lem7123962 {A : Type'} (P : type686 A) : term26 A P.
Proof. exact (@lem7123961 A P). Qed.
Lemma lem7123963 {A B : Type'} (f : type1416 A B) : term66 A B f.
Proof. exact (@lem7123962 A (term67 A B f)). Qed.
Lemma lem7123964 {A B : Type'} (f : type1416 A B) : (term68 A B f) = (term69 A B f).
Proof. exact (eq_refl (term68 A B f)). Qed.
Lemma lem7123965 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7123966 {A B : Type'} (f : type1416 A B) : (term70 A B f) = (term71 A B f).
Proof. exact (MK_COMB (@lem7123965) (@lem7123964 A B f)). Qed.
Lemma lem7123967 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term72 A B f s) = (term60 A B s f).
Proof. exact (eq_refl (term72 A B f s)). Qed.
Lemma lem7123968 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7123969 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term73 A B f s) = (term74 A B s f).
Proof. exact (MK_COMB (@lem7123968) (@lem7123967 A B s f)). Qed.
Lemma lem7123970 {A : Type'} (x : A) (s : A -> Prop) : (term75 A x s) = (term75 A x s).
Proof. exact (eq_refl (term75 A x s)). Qed.
Lemma lem7123971 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) : (term76 A B f x s) = (term77 A B f x s).
Proof. exact (MK_COMB (@lem7123969 A B s f) (@lem7123970 A x s)). Qed.
Lemma lem7123972 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7123973 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) : (term78 A B f x s) = (term79 A B f x s).
Proof. exact (MK_COMB (@lem7123972) (@lem7123971 A B f x s)). Qed.
Lemma lem7123974 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) : (term80 A B f x s) = (term81 A B x s f).
Proof. exact (eq_refl (term80 A B f x s)). Qed.
Lemma lem7123975 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) : (term82 A B f x s) = (term83 A B x s f).
Proof. exact (MK_COMB (@lem7123973 A B f x s) (@lem7123974 A B x s f)). Qed.
Lemma lem7123976 {A B : Type'} (x : A) (f : type1416 A B) : (term84 A B f x) = (term85 A B x f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7123975 A B x s f)). Qed.
Lemma lem7123977 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7123978 {A B : Type'} (x : A) (f : type1416 A B) : (term86 A B f x) = (term87 A B x f).
Proof. exact (MK_COMB (@lem7123977 A) (@lem7123976 A B x f)). Qed.
Lemma lem7123979 {A B : Type'} (f : type1416 A B) : (term88 A B f) = (term89 A B f).
Proof. exact (fun_ext (fun x : A => @lem7123978 A B x f)). Qed.
Lemma lem7123980 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7123981 {A B : Type'} (f : type1416 A B) : (term90 A B f) = (term91 A B f).
Proof. exact (MK_COMB (@lem7123980 A) (@lem7123979 A B f)). Qed.
Lemma lem7123982 {A B : Type'} (f : type1416 A B) : (term92 A B f) = (term93 A B f).
Proof. exact (MK_COMB (@lem7123966 A B f) (@lem7123981 A B f)). Qed.
Lemma lem7123983 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7123984 {A B : Type'} (f : type1416 A B) : (term94 A B f) = (term95 A B f).
Proof. exact (MK_COMB (@lem7123983) (@lem7123982 A B f)). Qed.
Lemma lem7123985 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term72 A B f s) = (term60 A B s f).
Proof. exact (eq_refl (term72 A B f s)). Qed.
Lemma lem7123986 {A : Type'} (s : A -> Prop) : (term53 A s) = (term53 A s).
Proof. exact (eq_refl (term53 A s)). Qed.
Lemma lem7123987 {A B : Type'} (s : A -> Prop) (f : type1416 A B) : (term96 A B f s) = (term61 A B s f).
Proof. exact (MK_COMB (@lem7123986 A s) (@lem7123985 A B s f)). Qed.
Lemma lem7123988 {A B : Type'} (f : type1416 A B) : (term97 A B f) = (term63 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7123987 A B s f)). Qed.
Lemma lem7123989 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7123990 {A B : Type'} (f : type1416 A B) : (term98 A B f) = (term65 A B f).
Proof. exact (MK_COMB (@lem7123989 A) (@lem7123988 A B f)). Qed.
Lemma lem7123991 {A B : Type'} (f : type1416 A B) : (term66 A B f) = (term99 A B f).
Proof. exact (MK_COMB (@lem7123984 A B f) (@lem7123990 A B f)). Qed.
Lemma lem7123992 {A B : Type'} (f : type1416 A B) : term99 A B f.
Proof. exact (EQ_MP (@lem7123991 A B f) (@lem7123963 A B f)). Qed.
Lemma lem7124002 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7124003 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7124002 p q p' q'). Qed.
Lemma lem7124004 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7124003 p q p'). Qed.
Lemma lem7124005 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : term103 A B t f.
Proof. exact (@lem7124004 (@FINITE B t) ((term104 A B t f) = (term105 A B t f))). Qed.
Lemma lem7124006 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (p' : Prop) : term106 A B t f p'.
Proof. exact (@lem7124005 A B t f p'). Qed.
Lemma lem7124007 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (p' : Prop) : (term106 A B t f p') = (term107 A B t f p').
Proof. exact (eq_refl (term106 A B t f p')). Qed.
Lemma lem7124008 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (p' : Prop) : term107 A B t f p'.
Proof. exact (EQ_MP (@lem7124007 A B t f p') (@lem7124006 A B t f p')). Qed.
Lemma lem7124009 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : term108 A B t f p' q'.
Proof. exact (@lem7124008 A B t f p' q'). Qed.
Lemma lem7124010 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : (term108 A B t f p' q') = (term109 A B t f p' q').
Proof. exact (eq_refl (term108 A B t f p' q')). Qed.
Lemma lem7124011 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : term109 A B t f p' q'.
Proof. exact (EQ_MP (@lem7124010 A B t f p' q') (@lem7124009 A B t f p' q')). Qed.
Lemma lem7124012 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem7124013 {A B : Type'} (f : type1416 A B) (t : B -> Prop) (q' : Prop) : term110 A B f t q'.
Proof. exact (@lem7124011 A B t f (@FINITE B t) q'). Qed.
Lemma lem7124014 {A B : Type'} (f : type1416 A B) (t : B -> Prop) (q' : Prop) : term111 A B f t q'.
Proof. exact (@lem7124013 A B f t q' (@lem7124012 B t)). Qed.
Lemma lem7124021 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term12.
Proof. exact (EQ_MP (@lem7123817 _131483 f) (@lem7123816 _131483 f)). Qed.
Lemma lem7124022 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term12.
Proof. exact (@lem7124021 A f). Qed.
Lemma lem7124023 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : (term104 A B t f) = term12.
Proof. exact (@lem7124022 A (term112 A B t f)). Qed.
Lemma lem7124024 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124025 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : (term113 A B t f) = term114.
Proof. exact (MK_COMB (@lem7124024) (@lem7124023 A B t f)). Qed.
Lemma lem7124027 {_131483 : Type'} (f : _131483 -> real) : (@sum _131483 (@EMPTY _131483) f) = term12.
Proof. exact (EQ_MP (@lem7123817 _131483 f) (@lem7123816 _131483 f)). Qed.
Lemma lem7124028 {A : Type'} (f : A -> real) : (@sum A (@EMPTY A) f) = term12.
Proof. exact (@lem7124027 A f). Qed.
Lemma lem7124029 {A B : Type'} (f : type1416 A B) (j : B) : (term115 A B f j) = term12.
Proof. exact (@lem7124028 A (term116 A B f j)). Qed.
Lemma lem7124030 {A B : Type'} (f : type1416 A B) : (term117 A B f) = (term118 B).
Proof. exact (fun_ext (fun j : B => @lem7124029 A B f j)). Qed.
Lemma lem7124031 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7124032 {A B : Type'} (f : type1416 A B) (t : B -> Prop) : (term105 A B t f) = (term11 B t).
Proof. exact (MK_COMB (@lem7124031 B t) (@lem7124030 A B f)). Qed.
Lemma lem7124034 {A : Type'} (s : A -> Prop) : (term11 A s) = term12.
Proof. exact (EQ_MP (@lem7123796 A s) (@lem7123795 A s)). Qed.
Lemma lem7124035 {B : Type'} (s : B -> Prop) : (term11 B s) = term12.
Proof. exact (@lem7124034 B s). Qed.
Lemma lem7124036 {B : Type'} (t : B -> Prop) : (term11 B t) = term12.
Proof. exact (@lem7124035 B t). Qed.
Lemma lem7124037 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : (term105 A B t f) = term12.
Proof. exact (TRANS (@lem7124032 A B f t) (@lem7124036 B t)). Qed.
Lemma lem7124038 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : ((term104 A B t f) = (term105 A B t f)) = (term12 = term12).
Proof. exact (MK_COMB (@lem7124025 A B t f) (@lem7124037 A B t f)). Qed.
Lemma lem7124040 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7124041 (x : real) : (x = x) = True.
Proof. exact (@lem7124040 real x). Qed.
Lemma lem7124042 : (term12 = term12) = True.
Proof. exact (@lem7124041 term12). Qed.
Lemma lem7124043 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : ((term104 A B t f) = (term105 A B t f)) = True.
Proof. exact (TRANS (@lem7124038 A B t f) (@lem7124042)). Qed.
Lemma lem7124044 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : term119 A B t f.
Proof. exact (fun h0 : @FINITE B t => @lem7124043 A B t f). Qed.
Lemma lem7124045 {A B : Type'} (f : type1416 A B) (t : B -> Prop) : term120 A B f t.
Proof. exact (@lem7124014 A B f t True). Qed.
Lemma lem7124046 {A B : Type'} (f : type1416 A B) (t : B -> Prop) : (term121 A B t f) = (term122 B t).
Proof. exact (@lem7124045 A B f t (@lem7124044 A B t f)). Qed.
Lemma lem7124048 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7124049 {B : Type'} (t : B -> Prop) : (term122 B t) = True.
Proof. exact (@lem7124048 (@FINITE B t)). Qed.
Lemma lem7124050 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : (term121 A B t f) = True.
Proof. exact (TRANS (@lem7124046 A B f t) (@lem7124049 B t)). Qed.
Lemma lem7124051 {A B : Type'} (f : type1416 A B) : (term123 A B f) = (term124 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7124050 A B t f)). Qed.
Lemma lem7124052 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7124053 {A B : Type'} (f : type1416 A B) : (term69 A B f) = (term125 B).
Proof. exact (MK_COMB (@lem7124052 B) (@lem7124051 A B f)). Qed.
Lemma lem7124055 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124056 {B : Type'} (t : Prop) : (term127 B t) = t.
Proof. exact (@lem7124055 (B -> Prop) t). Qed.
Lemma lem7124057 {B : Type'} : (term125 B) = True.
Proof. exact (@lem7124056 B True). Qed.
Lemma lem7124058 {A B : Type'} (f : type1416 A B) : (term69 A B f) = True.
Proof. exact (TRANS (@lem7124053 A B f) (@lem7124057 B)). Qed.
Lemma lem7124059 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7124060 {A B : Type'} (f : type1416 A B) : (term71 A B f) = (and True).
Proof. exact (MK_COMB (@lem7124059) (@lem7124058 A B f)). Qed.
Lemma lem7124072 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7124073 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7124072 p q p' q'). Qed.
Lemma lem7124074 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7124073 p q p'). Qed.
Lemma lem7124075 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) : term128 A B x s f.
Proof. exact (@lem7124074 (term77 A B f x s) (term81 A B x s f)). Qed.
Lemma lem7124076 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) : term129 A B x s f p'.
Proof. exact (@lem7124075 A B x s f p'). Qed.
Lemma lem7124077 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) : (term129 A B x s f p') = (term130 A B x s f p').
Proof. exact (eq_refl (term129 A B x s f p')). Qed.
Lemma lem7124078 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) : term130 A B x s f p'.
Proof. exact (EQ_MP (@lem7124077 A B x s f p') (@lem7124076 A B x s f p')). Qed.
Lemma lem7124079 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : term131 A B x s f p' q'.
Proof. exact (@lem7124078 A B x s f p' q'). Qed.
Lemma lem7124080 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : (term131 A B x s f p' q') = (term132 A B x s f p' q').
Proof. exact (eq_refl (term131 A B x s f p' q')). Qed.
Lemma lem7124081 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : term132 A B x s f p' q'.
Proof. exact (EQ_MP (@lem7124080 A B x s f p' q') (@lem7124079 A B x s f p' q')). Qed.
Lemma lem7124117 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) : (term77 A B f x s) = (term77 A B f x s).
Proof. exact (eq_refl (term77 A B f x s)). Qed.
Lemma lem7124118 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (q' : Prop) : term133 A B f x s q'.
Proof. exact (@lem7124081 A B x s f (term77 A B f x s) q'). Qed.
Lemma lem7124119 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (q' : Prop) : term134 A B f x s q'.
Proof. exact (@lem7124118 A B f x s q' (@lem7124117 A B f x s)). Qed.
Lemma lem7124120 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term77 A B f x s.
Proof. exact (h1). Qed.
Lemma lem7124121 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term75 A x s.
Proof. exact (proj2 (@lem7124120 A B f x s h1)). Qed.
Lemma lem7124122 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : @FINITE A s.
Proof. exact (proj2 (@lem7124121 A B f x s h1)). Qed.
Lemma lem7124123 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem7124125 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term135 A x s.
Proof. exact (proj1 (@lem7124121 A B f x s h1)). Qed.
Lemma lem7124126 {A : Type'} (x : A) (s : A -> Prop) : term136 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem7124128 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term60 A B s f.
Proof. exact (proj1 (@lem7124120 A B f x s h1)). Qed.
Lemma lem7124129 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term51 A B s f t.
Proof. exact (@lem7124128 A B f x s h1 t). Qed.
Lemma lem7124130 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term51 A B s f t) = (term52 A B t s f).
Proof. exact (eq_refl (term51 A B s f t)). Qed.
Lemma lem7124131 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term52 A B t s f.
Proof. exact (EQ_MP (@lem7124130 A B t s f) (@lem7124129 A B t f x s h1)). Qed.
Lemma lem7124132 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem7124133 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term40 A B s t f) = (term41 A B t s f).
Proof. exact (@lem7124131 A B t f x s h2 (@lem7124132 B t h1)). Qed.
Lemma lem7124146 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term100 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7124147 (p : Prop) (q : Prop) (p' : Prop) : term101 p q p'.
Proof. exact (fun q' : Prop => @lem7124146 p q p' q'). Qed.
Lemma lem7124148 (p : Prop) (q : Prop) : term102 p q.
Proof. exact (fun p' : Prop => @lem7124147 p q p'). Qed.
Lemma lem7124149 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) : term137 A B t x s f.
Proof. exact (@lem7124148 (@FINITE B t) ((term138 A B x s t f) = (term139 A B t x s f))). Qed.
Lemma lem7124150 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) : term140 A B t x s f p'.
Proof. exact (@lem7124149 A B t x s f p'). Qed.
Lemma lem7124151 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) : (term140 A B t x s f p') = (term141 A B t x s f p').
Proof. exact (eq_refl (term140 A B t x s f p')). Qed.
Lemma lem7124152 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) : term141 A B t x s f p'.
Proof. exact (EQ_MP (@lem7124151 A B t x s f p') (@lem7124150 A B t x s f p')). Qed.
Lemma lem7124153 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : term142 A B t x s f p' q'.
Proof. exact (@lem7124152 A B t x s f p' q'). Qed.
Lemma lem7124154 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : (term142 A B t x s f p' q') = (term143 A B t x s f p' q').
Proof. exact (eq_refl (term142 A B t x s f p' q')). Qed.
Lemma lem7124155 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) (p' : Prop) (q' : Prop) : term143 A B t x s f p' q'.
Proof. exact (EQ_MP (@lem7124154 A B t x s f p' q') (@lem7124153 A B t x s f p' q')). Qed.
Lemma lem7124156 {B : Type'} (t : B -> Prop) : (@FINITE B t) = (@FINITE B t).
Proof. exact (eq_refl (@FINITE B t)). Qed.
Lemma lem7124157 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) (q' : Prop) : term144 A B x s f t q'.
Proof. exact (@lem7124155 A B t x s f (@FINITE B t) q'). Qed.
Lemma lem7124158 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) (q' : Prop) : term145 A B x s f t q'.
Proof. exact (@lem7124157 A B x s f t q' (@lem7124156 B t)). Qed.
Lemma lem7124159 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem7124160 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem7124165 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term19 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7123809 _131524 x f s h0). Qed.
Lemma lem7124166 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term19 A x s f.
Proof. exact (@lem7124165 A x s f). Qed.
Lemma lem7124167 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) : term146 A B x s t f.
Proof. exact (@lem7124166 A x s (term112 A B t f)). Qed.
Lemma lem7124169 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7124123 A s) (@lem7124122 A B f x s h1)). Qed.
Lemma lem7124170 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7124169 A B f x s h1)). Qed.
Lemma lem7124171 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7124170 A B f x s h1) (@lem0)). Qed.
Lemma lem7124172 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term138 A B x s t f) = (term147 A B x s t f).
Proof. exact (@lem7124167 A B x s t f (@lem7124171 A B f x s h1)). Qed.
Lemma lem7124174 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term148 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7124175 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term149 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7124174 _2963 g t e g' t' e'). Qed.
Lemma lem7124176 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term150 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7124175 _2963 g t e g' t'). Qed.
Lemma lem7124177 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term151 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7124176 _2963 g t e g'). Qed.
Lemma lem7124178 (g : Prop) (t : real) (e : real) : term152 g t e.
Proof. exact (@lem7124177 real g t e). Qed.
Lemma lem7124179 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) : term153 A B x s t f.
Proof. exact (@lem7124178 (@IN A x s) (term40 A B s t f) (term154 A B x s t f)). Qed.
Lemma lem7124180 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) : term155 A B x s t f g'.
Proof. exact (@lem7124179 A B x s t f g'). Qed.
Lemma lem7124181 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) : (term155 A B x s t f g') = (term156 A B x s t f g').
Proof. exact (eq_refl (term155 A B x s t f g')). Qed.
Lemma lem7124182 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) : term156 A B x s t f g'.
Proof. exact (EQ_MP (@lem7124181 A B x s t f g') (@lem7124180 A B x s t f g')). Qed.
Lemma lem7124183 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) (t' : real) : term157 A B x s t f g' t'.
Proof. exact (@lem7124182 A B x s t f g' t'). Qed.
Lemma lem7124184 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) (t' : real) : (term157 A B x s t f g' t') = (term158 A B x s t f g' t').
Proof. exact (eq_refl (term157 A B x s t f g' t')). Qed.
Lemma lem7124185 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) (t' : real) : term158 A B x s t f g' t'.
Proof. exact (EQ_MP (@lem7124184 A B x s t f g' t') (@lem7124183 A B x s t f g' t')). Qed.
Lemma lem7124186 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) (t' : real) (e' : real) : term159 A B x s t f g' t' e'.
Proof. exact (@lem7124185 A B x s t f g' t' e'). Qed.
Lemma lem7124187 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) (t' : real) (e' : real) : (term159 A B x s t f g' t' e') = (term160 A B x s t f g' t' e').
Proof. exact (eq_refl (term159 A B x s t f g' t' e')). Qed.
Lemma lem7124188 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (g' : Prop) (t' : real) (e' : real) : term160 A B x s t f g' t' e'.
Proof. exact (EQ_MP (@lem7124187 A B x s t f g' t' e') (@lem7124186 A B x s t f g' t' e')). Qed.
Lemma lem7124190 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (@IN A x s) = False.
Proof. exact (@lem7124126 A x s (@lem7124125 A B f x s h1)). Qed.
Lemma lem7124191 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (f : type1416 A B) (t' : real) (e' : real) : term161 A B x s t f t' e'.
Proof. exact (@lem7124188 A B x s t f False t' e'). Qed.
Lemma lem7124192 {A B : Type'} (t : B -> Prop) (t' : real) (e' : real) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term162 A B x s t f t' e'.
Proof. exact (@lem7124191 A B x s t f t' e' (@lem7124190 A B f x s h1)). Qed.
Lemma lem7124197 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term52 A B t s f.
Proof. exact (fun h0 : @FINITE B t => @lem7124133 A B t f x s h0 h1). Qed.
Lemma lem7124198 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term52 A B t s f.
Proof. exact (@lem7124197 A B t f x s h1). Qed.
Lemma lem7124200 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7124160 B t) (@lem7124159 B t h1)). Qed.
Lemma lem7124201 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7124200 B t h1)). Qed.
Lemma lem7124202 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7124201 B t h1) (@lem0)). Qed.
Lemma lem7124203 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term40 A B s t f) = (term41 A B t s f).
Proof. exact (@lem7124198 A B t f x s h2 (@lem7124202 B t h1)). Qed.
Lemma lem7124204 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : term163 A B t s f.
Proof. exact (fun h0 : False => @lem7124203 A B t f x s h1 h2). Qed.
Lemma lem7124205 {A B : Type'} (t : B -> Prop) (e' : real) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term164 A B x t s f e'.
Proof. exact (@lem7124192 A B t (term41 A B t s f) e' f x s h1). Qed.
Lemma lem7124206 {A B : Type'} (e' : real) (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : term165 A B x t s f e'.
Proof. exact (@lem7124205 A B t e' f x s h2 (@lem7124204 A B t f x s h1 h2)). Qed.
Lemma lem7124213 {A B : Type'} (f : A -> B) (y : A) : (term166 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7124214 {A : Type'} (f : A -> real) (y : A) : (term167 A f y) = (f y).
Proof. exact (@lem7124213 A real f y). Qed.
Lemma lem7124215 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term168 A B t f x) = (term169 A B t f x).
Proof. exact (@lem7124214 A (term112 A B t f) x). Qed.
Lemma lem7124216 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (i : A) : (term169 A B t f i) = (term170 A B t f i).
Proof. exact (eq_refl (term169 A B t f i)). Qed.
Lemma lem7124217 {A B : Type'} (t : B -> Prop) (f : type1416 A B) : (term171 A B t f) = (term112 A B t f).
Proof. exact (fun_ext (fun i : A => @lem7124216 A B t f i)). Qed.
Lemma lem7124218 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7124219 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term168 A B t f x) = (term169 A B t f x).
Proof. exact (MK_COMB (@lem7124217 A B t f) (@lem7124218 A x)). Qed.
Lemma lem7124220 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124221 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term172 A B t f x) = (term173 A B t f x).
Proof. exact (MK_COMB (@lem7124220) (@lem7124219 A B t f x)). Qed.
Lemma lem7124222 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term169 A B t f x) = (term170 A B t f x).
Proof. exact (eq_refl (term169 A B t f x)). Qed.
Lemma lem7124223 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : ((term168 A B t f x) = (term169 A B t f x)) = ((term169 A B t f x) = (term170 A B t f x)).
Proof. exact (MK_COMB (@lem7124221 A B t f x) (@lem7124222 A B t f x)). Qed.
Lemma lem7124224 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term169 A B t f x) = (term170 A B t f x).
Proof. exact (EQ_MP (@lem7124223 A B t f x) (@lem7124215 A B t f x)). Qed.
Lemma lem7124225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7124226 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term174 A B t f x) = (term175 A B t f x).
Proof. exact (MK_COMB (@lem7124225) (@lem7124224 A B t f x)). Qed.
Lemma lem7124228 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term52 A B t s f.
Proof. exact (fun h0 : @FINITE B t => @lem7124133 A B t f x s h0 h1). Qed.
Lemma lem7124229 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term52 A B t s f.
Proof. exact (@lem7124228 A B t f x s h1). Qed.
Lemma lem7124231 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7124160 B t) (@lem7124159 B t h1)). Qed.
Lemma lem7124232 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7124231 B t h1)). Qed.
Lemma lem7124233 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7124232 B t h1) (@lem0)). Qed.
Lemma lem7124234 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term40 A B s t f) = (term41 A B t s f).
Proof. exact (@lem7124229 A B t f x s h2 (@lem7124233 B t h1)). Qed.
Lemma lem7124235 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term154 A B x s t f) = (term176 A B x t s f).
Proof. exact (MK_COMB (@lem7124226 A B t f x) (@lem7124234 A B t f x s h1 h2)). Qed.
Lemma lem7124236 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : term177 A B x t s f.
Proof. exact (fun h0 : ~ False => @lem7124235 A B t f x s h1 h2). Qed.
Lemma lem7124237 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : term178 A B x t s f.
Proof. exact (@lem7124206 A B (term176 A B x t s f) t f x s h1 h2). Qed.
Lemma lem7124238 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term147 A B x s t f) = (term179 A B x t s f).
Proof. exact (@lem7124237 A B t f x s h1 h2 (@lem7124236 A B t f x s h1 h2)). Qed.
Lemma lem7124240 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7124241 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7124240 real t1 t2). Qed.
Lemma lem7124242 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term179 A B x t s f) = (term176 A B x t s f).
Proof. exact (@lem7124241 (term41 A B t s f) (term176 A B x t s f)). Qed.
Lemma lem7124243 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term147 A B x s t f) = (term176 A B x t s f).
Proof. exact (TRANS (@lem7124238 A B t f x s h1 h2) (@lem7124242 A B x t s f)). Qed.
Lemma lem7124244 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term138 A B x s t f) = (term176 A B x t s f).
Proof. exact (TRANS (@lem7124172 A B t f x s h2) (@lem7124243 A B t f x s h1 h2)). Qed.
Lemma lem7124245 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124246 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term180 A B x s t f) = (term181 A B x t s f).
Proof. exact (MK_COMB (@lem7124245) (@lem7124244 A B t f x s h1 h2)). Qed.
Lemma lem7124248 {_131524 : Type'} (x : _131524) (s : _131524 -> Prop) (f : _131524 -> real) : term19 _131524 x s f.
Proof. exact (fun h0 : @FINITE _131524 s => @lem7123809 _131524 x f s h0). Qed.
Lemma lem7124249 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : term19 A x s f.
Proof. exact (@lem7124248 A x s f). Qed.
Lemma lem7124250 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) : term182 A B x s f j.
Proof. exact (@lem7124249 A x s (term116 A B f j)). Qed.
Lemma lem7124252 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem7124123 A s) (@lem7124122 A B f x s h1)). Qed.
Lemma lem7124253 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : True = (@FINITE A s).
Proof. exact (SYM (@lem7124252 A B f x s h1)). Qed.
Lemma lem7124254 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7124253 A B f x s h1) (@lem0)). Qed.
Lemma lem7124255 {A B : Type'} (j : B) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term183 A B x s f j) = (term184 A B x s f j).
Proof. exact (@lem7124250 A B x s f j (@lem7124254 A B f x s h1)). Qed.
Lemma lem7124257 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term148 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem7124258 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term149 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem7124257 _2963 g t e g' t' e'). Qed.
Lemma lem7124259 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term150 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem7124258 _2963 g t e g' t'). Qed.
Lemma lem7124260 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term151 _2963 g t e.
Proof. exact (fun g' : Prop => @lem7124259 _2963 g t e g'). Qed.
Lemma lem7124261 (g : Prop) (t : real) (e : real) : term152 g t e.
Proof. exact (@lem7124260 real g t e). Qed.
Lemma lem7124262 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) : term185 A B x s f j.
Proof. exact (@lem7124261 (@IN A x s) (term186 A B s f j) (term187 A B x s f j)). Qed.
Lemma lem7124263 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) : term188 A B x s f j g'.
Proof. exact (@lem7124262 A B x s f j g'). Qed.
Lemma lem7124264 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) : (term188 A B x s f j g') = (term189 A B x s f j g').
Proof. exact (eq_refl (term188 A B x s f j g')). Qed.
Lemma lem7124265 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) : term189 A B x s f j g'.
Proof. exact (EQ_MP (@lem7124264 A B x s f j g') (@lem7124263 A B x s f j g')). Qed.
Lemma lem7124266 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) (t' : real) : term190 A B x s f j g' t'.
Proof. exact (@lem7124265 A B x s f j g' t'). Qed.
Lemma lem7124267 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) (t' : real) : (term190 A B x s f j g' t') = (term191 A B x s f j g' t').
Proof. exact (eq_refl (term190 A B x s f j g' t')). Qed.
Lemma lem7124268 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) (t' : real) : term191 A B x s f j g' t'.
Proof. exact (EQ_MP (@lem7124267 A B x s f j g' t') (@lem7124266 A B x s f j g' t')). Qed.
Lemma lem7124269 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) (t' : real) (e' : real) : term192 A B x s f j g' t' e'.
Proof. exact (@lem7124268 A B x s f j g' t' e'). Qed.
Lemma lem7124270 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) (t' : real) (e' : real) : (term192 A B x s f j g' t' e') = (term193 A B x s f j g' t' e').
Proof. exact (eq_refl (term192 A B x s f j g' t' e')). Qed.
Lemma lem7124271 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (g' : Prop) (t' : real) (e' : real) : term193 A B x s f j g' t' e'.
Proof. exact (EQ_MP (@lem7124270 A B x s f j g' t' e') (@lem7124269 A B x s f j g' t' e')). Qed.
Lemma lem7124273 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (@IN A x s) = False.
Proof. exact (@lem7124126 A x s (@lem7124125 A B f x s h1)). Qed.
Lemma lem7124274 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) (t' : real) (e' : real) : term194 A B x s f j t' e'.
Proof. exact (@lem7124271 A B x s f j False t' e'). Qed.
Lemma lem7124275 {A B : Type'} (j : B) (t' : real) (e' : real) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term195 A B x s f j t' e'.
Proof. exact (@lem7124274 A B x s f j t' e' (@lem7124273 A B f x s h1)). Qed.
Lemma lem7124279 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (j : B) : (term186 A B s f j) = (term186 A B s f j).
Proof. exact (eq_refl (term186 A B s f j)). Qed.
Lemma lem7124280 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (j : B) : term196 A B s f j.
Proof. exact (fun h0 : False => @lem7124279 A B s f j). Qed.
Lemma lem7124281 {A B : Type'} (j : B) (e' : real) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term197 A B x s f j e'.
Proof. exact (@lem7124275 A B j (term186 A B s f j) e' f x s h1). Qed.
Lemma lem7124282 {A B : Type'} (j : B) (e' : real) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term198 A B x s f j e'.
Proof. exact (@lem7124281 A B j e' f x s h1 (@lem7124280 A B s f j)). Qed.
Lemma lem7124289 {A B : Type'} (f : A -> B) (y : A) : (term166 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7124290 {A : Type'} (f : A -> real) (y : A) : (term167 A f y) = (f y).
Proof. exact (@lem7124289 A real f y). Qed.
Lemma lem7124291 {A B : Type'} (f : type1416 A B) (j : B) (x : A) : (term199 A B f j x) = (term200 A B f j x).
Proof. exact (@lem7124290 A (term116 A B f j) x). Qed.
Lemma lem7124292 {A B : Type'} (f : type1416 A B) (i : A) (j : B) : (term200 A B f j i) = (f i j).
Proof. exact (eq_refl (term200 A B f j i)). Qed.
Lemma lem7124293 {A B : Type'} (f : type1416 A B) (j : B) : (term201 A B f j) = (term116 A B f j).
Proof. exact (fun_ext (fun i : A => @lem7124292 A B f i j)). Qed.
Lemma lem7124294 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7124295 {A B : Type'} (f : type1416 A B) (j : B) (x : A) : (term199 A B f j x) = (term200 A B f j x).
Proof. exact (MK_COMB (@lem7124293 A B f j) (@lem7124294 A x)). Qed.
Lemma lem7124296 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124297 {A B : Type'} (f : type1416 A B) (j : B) (x : A) : (term202 A B f j x) = (term203 A B f j x).
Proof. exact (MK_COMB (@lem7124296) (@lem7124295 A B f j x)). Qed.
Lemma lem7124298 {A B : Type'} (f : type1416 A B) (x : A) (j : B) : (term200 A B f j x) = (f x j).
Proof. exact (eq_refl (term200 A B f j x)). Qed.
Lemma lem7124299 {A B : Type'} (f : type1416 A B) (x : A) (j : B) : ((term199 A B f j x) = (term200 A B f j x)) = ((term200 A B f j x) = (f x j)).
Proof. exact (MK_COMB (@lem7124297 A B f j x) (@lem7124298 A B f x j)). Qed.
Lemma lem7124300 {A B : Type'} (f : type1416 A B) (x : A) (j : B) : (term200 A B f j x) = (f x j).
Proof. exact (EQ_MP (@lem7124299 A B f x j) (@lem7124291 A B f j x)). Qed.
Lemma lem7124301 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7124302 {A B : Type'} (f : type1416 A B) (x : A) (j : B) : (term204 A B f j x) = (term205 A B f x j).
Proof. exact (MK_COMB (@lem7124301) (@lem7124300 A B f x j)). Qed.
Lemma lem7124303 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (j : B) : (term186 A B s f j) = (term186 A B s f j).
Proof. exact (eq_refl (term186 A B s f j)). Qed.
Lemma lem7124304 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) : (term187 A B x s f j) = (term206 A B x s f j).
Proof. exact (MK_COMB (@lem7124302 A B f x j) (@lem7124303 A B s f j)). Qed.
Lemma lem7124305 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) : term207 A B x s f j.
Proof. exact (fun h0 : ~ False => @lem7124304 A B x s f j). Qed.
Lemma lem7124306 {A B : Type'} (j : B) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term208 A B x s f j.
Proof. exact (@lem7124282 A B j (term206 A B x s f j) f x s h1). Qed.
Lemma lem7124307 {A B : Type'} (j : B) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term184 A B x s f j) = (term209 A B x s f j).
Proof. exact (@lem7124306 A B j f x s h1 (@lem7124305 A B x s f j)). Qed.
Lemma lem7124309 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem7124310 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem7124309 real t1 t2). Qed.
Lemma lem7124311 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) : (term209 A B x s f j) = (term206 A B x s f j).
Proof. exact (@lem7124310 (term186 A B s f j) (term206 A B x s f j)). Qed.
Lemma lem7124312 {A B : Type'} (j : B) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term184 A B x s f j) = (term206 A B x s f j).
Proof. exact (TRANS (@lem7124307 A B j f x s h1) (@lem7124311 A B x s f j)). Qed.
Lemma lem7124313 {A B : Type'} (j : B) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term183 A B x s f j) = (term206 A B x s f j).
Proof. exact (TRANS (@lem7124255 A B j f x s h1) (@lem7124312 A B j f x s h1)). Qed.
Lemma lem7124314 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term210 A B x s f) = (term211 A B x s f).
Proof. exact (fun_ext (fun j : B => @lem7124313 A B j f x s h1)). Qed.
Lemma lem7124315 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7124316 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term139 A B t x s f) = (term212 A B t x s f).
Proof. exact (MK_COMB (@lem7124315 B t) (@lem7124314 A B f x s h1)). Qed.
Lemma lem7124318 {_131713 : Type'} (f : _131713 -> real) (s : _131713 -> Prop) (g : _131713 -> real) : term7 _131713 f s g.
Proof. exact (fun h0 : @FINITE _131713 s => @lem7123789 _131713 f g s h0). Qed.
Lemma lem7124319 {B : Type'} (f : B -> real) (s : B -> Prop) (g : B -> real) : term7 B f s g.
Proof. exact (@lem7124318 B f s g). Qed.
Lemma lem7124320 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : term213 A B x t s f.
Proof. exact (@lem7124319 B (term214 A B f x) t (term215 A B s f)). Qed.
Lemma lem7124321 {A B : Type'} (f : type1416 A B) (x : A) (j : B) : (term216 A B f x j) = (f x j).
Proof. exact (eq_refl (term216 A B f x j)). Qed.
Lemma lem7124322 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7124323 {A B : Type'} (f : type1416 A B) (x : A) (j : B) : (term217 A B f x j) = (term205 A B f x j).
Proof. exact (MK_COMB (@lem7124322) (@lem7124321 A B f x j)). Qed.
Lemma lem7124324 {A B : Type'} (s : A -> Prop) (f : type1416 A B) (j : B) : (term218 A B s f j) = (term186 A B s f j).
Proof. exact (eq_refl (term218 A B s f j)). Qed.
Lemma lem7124325 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (j : B) : (term219 A B x s f j) = (term206 A B x s f j).
Proof. exact (MK_COMB (@lem7124323 A B f x j) (@lem7124324 A B s f j)). Qed.
Lemma lem7124326 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) : (term220 A B x s f) = (term211 A B x s f).
Proof. exact (fun_ext (fun j : B => @lem7124325 A B x s f j)). Qed.
Lemma lem7124327 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7124328 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) : (term221 A B t x s f) = (term212 A B t x s f).
Proof. exact (MK_COMB (@lem7124327 B t) (@lem7124326 A B x s f)). Qed.
Lemma lem7124329 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7124330 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (f : type1416 A B) : (term222 A B t x s f) = (term223 A B t x s f).
Proof. exact (MK_COMB (@lem7124329) (@lem7124328 A B t x s f)). Qed.
Lemma lem7124331 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term224 A B x t s f) = (term224 A B x t s f).
Proof. exact (eq_refl (term224 A B x t s f)). Qed.
Lemma lem7124332 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : ((term221 A B t x s f) = (term224 A B x t s f)) = ((term212 A B t x s f) = (term224 A B x t s f)).
Proof. exact (MK_COMB (@lem7124330 A B t x s f) (@lem7124331 A B x t s f)). Qed.
Lemma lem7124333 {B : Type'} (t : B -> Prop) : (term53 B t) = (term53 B t).
Proof. exact (eq_refl (term53 B t)). Qed.
Lemma lem7124334 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term213 A B x t s f) = (term225 A B x t s f).
Proof. exact (MK_COMB (@lem7124333 B t) (@lem7124332 A B x t s f)). Qed.
Lemma lem7124335 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : term225 A B x t s f.
Proof. exact (EQ_MP (@lem7124334 A B x t s f) (@lem7124320 A B x t s f)). Qed.
Lemma lem7124337 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem7124160 B t) (@lem7124159 B t h1)). Qed.
Lemma lem7124338 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : True = (@FINITE B t).
Proof. exact (SYM (@lem7124337 B t h1)). Qed.
Lemma lem7124339 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (EQ_MP (@lem7124338 B t h1) (@lem0)). Qed.
Lemma lem7124340 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) (h1 : @FINITE B t) : (term212 A B t x s f) = (term224 A B x t s f).
Proof. exact (@lem7124335 A B x t s f (@lem7124339 B t h1)). Qed.
Lemma lem7124341 {B : Type'} (t : B -> real) : (term226 B t) = t.
Proof. exact (@lem7123778 B real t). Qed.
Lemma lem7124342 {A B : Type'} (f : type1416 A B) (x : A) : (term214 A B f x) = (f x).
Proof. exact (@lem7124341 B (f x)). Qed.
Lemma lem7124343 {B : Type'} (t : B -> Prop) : (@sum B t) = (@sum B t).
Proof. exact (eq_refl (@sum B t)). Qed.
Lemma lem7124344 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term227 A B t f x) = (term170 A B t f x).
Proof. exact (MK_COMB (@lem7124343 B t) (@lem7124342 A B f x)). Qed.
Lemma lem7124345 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7124346 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) : (term228 A B t f x) = (term175 A B t f x).
Proof. exact (MK_COMB (@lem7124345) (@lem7124344 A B t f x)). Qed.
Lemma lem7124347 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term41 A B t s f) = (term41 A B t s f).
Proof. exact (eq_refl (term41 A B t s f)). Qed.
Lemma lem7124348 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : (term224 A B x t s f) = (term176 A B x t s f).
Proof. exact (MK_COMB (@lem7124346 A B t f x) (@lem7124347 A B t s f)). Qed.
Lemma lem7124349 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) (h1 : @FINITE B t) : (term212 A B t x s f) = (term176 A B x t s f).
Proof. exact (TRANS (@lem7124340 A B x s f t h1) (@lem7124348 A B x t s f)). Qed.
Lemma lem7124350 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : (term139 A B t x s f) = (term176 A B x t s f).
Proof. exact (TRANS (@lem7124316 A B t f x s h2) (@lem7124349 A B x s f t h1)). Qed.
Lemma lem7124351 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : ((term138 A B x s t f) = (term139 A B t x s f)) = ((term176 A B x t s f) = (term176 A B x t s f)).
Proof. exact (MK_COMB (@lem7124246 A B t f x s h1 h2) (@lem7124350 A B t f x s h1 h2)). Qed.
Lemma lem7124353 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7124354 (x : real) : (x = x) = True.
Proof. exact (@lem7124353 real x). Qed.
Lemma lem7124355 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : type1416 A B) : ((term176 A B x t s f) = (term176 A B x t s f)) = True.
Proof. exact (@lem7124354 (term176 A B x t s f)). Qed.
Lemma lem7124356 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : @FINITE B t) (h2 : term77 A B f x s) : ((term138 A B x s t f) = (term139 A B t x s f)) = True.
Proof. exact (TRANS (@lem7124351 A B t f x s h1 h2) (@lem7124355 A B x t s f)). Qed.
Lemma lem7124357 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : term229 A B t x s f.
Proof. exact (fun h0 : @FINITE B t => @lem7124356 A B t f x s h0 h1). Qed.
Lemma lem7124358 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) (t : B -> Prop) : term230 A B x s f t.
Proof. exact (@lem7124158 A B x s f t True). Qed.
Lemma lem7124359 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term231 A B t x s f) = (term122 B t).
Proof. exact (@lem7124358 A B x s f t (@lem7124357 A B t f x s h1)). Qed.
Lemma lem7124361 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7124362 {B : Type'} (t : B -> Prop) : (term122 B t) = True.
Proof. exact (@lem7124361 (@FINITE B t)). Qed.
Lemma lem7124363 {A B : Type'} (t : B -> Prop) (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term231 A B t x s f) = True.
Proof. exact (TRANS (@lem7124359 A B t f x s h1) (@lem7124362 B t)). Qed.
Lemma lem7124364 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term232 A B x s f) = (term124 B).
Proof. exact (fun_ext (fun t : B -> Prop => @lem7124363 A B t f x s h1)). Qed.
Lemma lem7124365 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem7124366 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term81 A B x s f) = (term125 B).
Proof. exact (MK_COMB (@lem7124365 B) (@lem7124364 A B f x s h1)). Qed.
Lemma lem7124368 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124369 {B : Type'} (t : Prop) : (term127 B t) = t.
Proof. exact (@lem7124368 (B -> Prop) t). Qed.
Lemma lem7124370 {B : Type'} : (term125 B) = True.
Proof. exact (@lem7124369 B True). Qed.
Lemma lem7124371 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) (h1 : term77 A B f x s) : (term81 A B x s f) = True.
Proof. exact (TRANS (@lem7124366 A B f x s h1) (@lem7124370 B)). Qed.
Lemma lem7124372 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) : term233 A B x s f.
Proof. exact (fun h0 : term77 A B f x s => @lem7124371 A B f x s h0). Qed.
Lemma lem7124373 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) : term234 A B f x s.
Proof. exact (@lem7124119 A B f x s True). Qed.
Lemma lem7124374 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) : (term83 A B x s f) = (term235 A B f x s).
Proof. exact (@lem7124373 A B f x s (@lem7124372 A B x s f)). Qed.
Lemma lem7124376 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7124377 {A B : Type'} (f : type1416 A B) (x : A) (s : A -> Prop) : (term235 A B f x s) = True.
Proof. exact (@lem7124376 (term77 A B f x s)). Qed.
Lemma lem7124378 {A B : Type'} (x : A) (s : A -> Prop) (f : type1416 A B) : (term83 A B x s f) = True.
Proof. exact (TRANS (@lem7124374 A B f x s) (@lem7124377 A B f x s)). Qed.
Lemma lem7124379 {A B : Type'} (x : A) (f : type1416 A B) : (term85 A B x f) = (term124 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7124378 A B x s f)). Qed.
Lemma lem7124380 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7124381 {A B : Type'} (x : A) (f : type1416 A B) : (term87 A B x f) = (term125 A).
Proof. exact (MK_COMB (@lem7124380 A) (@lem7124379 A B x f)). Qed.
Lemma lem7124383 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124384 {A : Type'} (t : Prop) : (term127 A t) = t.
Proof. exact (@lem7124383 (A -> Prop) t). Qed.
Lemma lem7124385 {A : Type'} : (term125 A) = True.
Proof. exact (@lem7124384 A True). Qed.
Lemma lem7124386 {A B : Type'} (x : A) (f : type1416 A B) : (term87 A B x f) = True.
Proof. exact (TRANS (@lem7124381 A B x f) (@lem7124385 A)). Qed.
Lemma lem7124387 {A B : Type'} (f : type1416 A B) : (term89 A B f) = (term236 A).
Proof. exact (fun_ext (fun x : A => @lem7124386 A B x f)). Qed.
Lemma lem7124388 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7124389 {A B : Type'} (f : type1416 A B) : (term91 A B f) = (term237 A).
Proof. exact (MK_COMB (@lem7124388 A) (@lem7124387 A B f)). Qed.
Lemma lem7124391 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7124392 {A : Type'} (t : Prop) : (term126 A t) = t.
Proof. exact (@lem7124391 A t). Qed.
Lemma lem7124393 {A : Type'} : (term237 A) = True.
Proof. exact (@lem7124392 A True). Qed.
Lemma lem7124394 {A B : Type'} (f : type1416 A B) : (term91 A B f) = True.
Proof. exact (TRANS (@lem7124389 A B f) (@lem7124393 A)). Qed.
Lemma lem7124395 {A B : Type'} (f : type1416 A B) : (term93 A B f) = (True /\ True).
Proof. exact (MK_COMB (@lem7124060 A B f) (@lem7124394 A B f)). Qed.
Lemma lem7124397 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7124398 : (True /\ True) = True.
Proof. exact (@lem7124397 True). Qed.
Lemma lem7124399 {A B : Type'} (f : type1416 A B) : (term93 A B f) = True.
Proof. exact (TRANS (@lem7124395 A B f) (@lem7124398)). Qed.
Lemma lem7124400 {A B : Type'} (f : type1416 A B) : True = (term93 A B f).
Proof. exact (SYM (@lem7124399 A B f)). Qed.
Lemma lem7124401 {A B : Type'} (f : type1416 A B) : term93 A B f.
Proof. exact (EQ_MP (@lem7124400 A B f) (@lem0)). Qed.
Lemma lem7124402 {A B : Type'} (f : type1416 A B) : term65 A B f.
Proof. exact (@lem7123992 A B f (@lem7124401 A B f)). Qed.
Lemma lem7124403 {A B : Type'} (f : type1416 A B) : term64 A B f.
Proof. exact (EQ_MP (@lem7123959 A B f) (@lem7124402 A B f)). Qed.
Lemma lem7124408 {A B : Type'} : term238 A B.
Proof. exact (fun f : type1416 A B => @lem7124403 A B f). Qed.
