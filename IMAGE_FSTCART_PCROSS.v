Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IMAGE_FSTCART_PCROSS_term_abbrevs.
Require Import CONJ_SYM_spec.
Require Import EXTENSION_spec.
Require Import FSTCART_PASTECART_spec.
Require Import IMAGE_CLAUSES_spec.
Require Import IN_IMAGE_spec.
Require Import PCROSS_EMPTY_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16439_spec.
Require Import thm16440_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19006_spec.
Require Import thm19007_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8004099_spec.
Lemma lem8033713 {A M N : Type'} (x : cart A M) : term0 A M N x.
Proof. exact (@lem7643282 A M N x). Qed.
Lemma lem8033714 {A M N : Type'} (x : cart A M) : (term0 A M N x) = (term1 A M N x).
Proof. exact (eq_refl (term0 A M N x)). Qed.
Lemma lem8033715 {A M N : Type'} (x : cart A M) : term1 A M N x.
Proof. exact (EQ_MP (@lem8033714 A M N x) (@lem8033713 A M N x)). Qed.
Lemma lem8033716 {A M N : Type'} (x : cart A M) (y : cart A N) : term2 A M N x y.
Proof. exact (@lem8033715 A M N x y). Qed.
Lemma lem8033717 {A M N : Type'} (y : cart A N) (x : cart A M) : (term2 A M N x y) = ((term3 A M N x y) = x).
Proof. exact (eq_refl (term2 A M N x y)). Qed.
Lemma lem8033719 (t1 : Prop) : term4 t1.
Proof. exact (@lem539 t1). Qed.
Lemma lem8033720 (t1 : Prop) : (term4 t1) = (term5 t1).
Proof. exact (eq_refl (term4 t1)). Qed.
Lemma lem8033721 (t1 : Prop) : term5 t1.
Proof. exact (EQ_MP (@lem8033720 t1) (@lem8033719 t1)). Qed.
Lemma lem8033722 (t1 : Prop) (t2 : Prop) : term6 t1 t2.
Proof. exact (@lem8033721 t1 t2). Qed.
Lemma lem8033723 (t2 : Prop) (t1 : Prop) : (term6 t1 t2) = ((t1 /\ t2) = (t2 /\ t1)).
Proof. exact (eq_refl (term6 t1 t2)). Qed.
Lemma lem8033725 {A B : Type'} (y : B) : term7 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem8033726 {A B : Type'} (y : B) : (term7 A B y) = (term8 A B y).
Proof. exact (eq_refl (term7 A B y)). Qed.
Lemma lem8033727 {A B : Type'} (y : B) : term8 A B y.
Proof. exact (EQ_MP (@lem8033726 A B y) (@lem8033725 A B y)). Qed.
Lemma lem8033728 {A B : Type'} (y : B) (s : A -> Prop) : term9 A B y s.
Proof. exact (@lem8033727 A B y s). Qed.
Lemma lem8033729 {A B : Type'} (y : B) (s : A -> Prop) : (term9 A B y s) = (term10 A B y s).
Proof. exact (eq_refl (term9 A B y s)). Qed.
Lemma lem8033730 {A B : Type'} (y : B) (s : A -> Prop) : term10 A B y s.
Proof. exact (EQ_MP (@lem8033729 A B y s) (@lem8033728 A B y s)). Qed.
Lemma lem8033731 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term11 A B y s f.
Proof. exact (@lem8033730 A B y s f). Qed.
Lemma lem8033732 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term11 A B y s f) = ((term12 A B y f s) = (term13 A B y f s)).
Proof. exact (eq_refl (term11 A B y s f)). Qed.
Lemma lem8033734 {A : Type'} (s : A -> Prop) : term14 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem8033735 {A : Type'} (s : A -> Prop) : (term14 A s) = (term15 A s).
Proof. exact (eq_refl (term14 A s)). Qed.
Lemma lem8033736 {A : Type'} (s : A -> Prop) : term15 A s.
Proof. exact (EQ_MP (@lem8033735 A s) (@lem8033734 A s)). Qed.
Lemma lem8033737 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term16 A s t.
Proof. exact (@lem8033736 A s t). Qed.
Lemma lem8033738 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term16 A s t) = ((s = t) = (term17 A s t)).
Proof. exact (eq_refl (term16 A s t)). Qed.
Lemma lem8033740 {M : Type'} (_474 : type30 M) (_475 : Prop) (_476 : type58 M) (_477 : type30 M) : (term18 M _476 _475 _474 _477) = (term19 M _474 _475 _476 _477).
Proof. exact (@lem13473 (type30 M) _474 _475 _476 _477). Qed.
Lemma lem8033741 {M N : Type'} (_474 : type30 M) (_475 : Prop) (s : type30 M) (t : type30 N) (_477 : type30 M) : (term20 M N s t _475 _474 _477) = (term21 M N _474 _475 s t _477).
Proof. exact (@lem8033740 M _474 _475 (term22 M N s t) _477). Qed.
Lemma lem8033742 {M N : Type'} (t : type30 N) (s : type30 M) : (term23 M N t s) = (term24 M N t s).
Proof. exact (@lem8033741 M N (@EMPTY (cart real M)) (t = (@EMPTY (cart real N))) s t s). Qed.
Lemma lem8033743 {M N : Type'} (t : type30 N) (s : type30 M) : (term25 M N t s) = ((term26 M N s t) = s).
Proof. exact (eq_refl (term25 M N t s)). Qed.
Lemma lem8033744 {N : Type'} (t : type30 N) : (term27 N t) = (term27 N t).
Proof. exact (eq_refl (term27 N t)). Qed.
Lemma lem8033745 {M N : Type'} (t : type30 N) (s : type30 M) : (term28 M N t s) = (term29 M N t s).
Proof. exact (MK_COMB (@lem8033744 N t) (@lem8033743 M N t s)). Qed.
Lemma lem8033746 {M N : Type'} (s : type30 M) (t : type30 N) : (term30 M N s t) = ((term26 M N s t) = (@EMPTY (cart real M))).
Proof. exact (eq_refl (term30 M N s t)). Qed.
Lemma lem8033747 {N : Type'} (t : type30 N) : (term31 N t) = (term31 N t).
Proof. exact (eq_refl (term31 N t)). Qed.
Lemma lem8033748 {M N : Type'} (s : type30 M) (t : type30 N) : (term32 M N s t) = (term33 M N s t).
Proof. exact (MK_COMB (@lem8033747 N t) (@lem8033746 M N s t)). Qed.
Lemma lem8033749 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8033750 {M N : Type'} (s : type30 M) (t : type30 N) : (term34 M N s t) = (term35 M N s t).
Proof. exact (MK_COMB (@lem8033749) (@lem8033748 M N s t)). Qed.
Lemma lem8033751 {M N : Type'} (t : type30 N) (s : type30 M) : (term24 M N t s) = (term36 M N t s).
Proof. exact (MK_COMB (@lem8033750 M N s t) (@lem8033745 M N t s)). Qed.
Lemma lem8033752 {M N : Type'} (t : type30 N) (s : type30 M) : (term23 M N t s) = ((term26 M N s t) = (term37 M N t s)).
Proof. exact (eq_refl (term23 M N t s)). Qed.
Lemma lem8033753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8033754 {M N : Type'} (t : type30 N) (s : type30 M) : (term38 M N t s) = (term39 M N t s).
Proof. exact (MK_COMB (@lem8033753) (@lem8033752 M N t s)). Qed.
Lemma lem8033755 {M N : Type'} (t : type30 N) (s : type30 M) : ((term23 M N t s) = (term24 M N t s)) = (((term26 M N s t) = (term37 M N t s)) = (term36 M N t s)).
Proof. exact (MK_COMB (@lem8033754 M N t s) (@lem8033751 M N t s)). Qed.
Lemma lem8033756 {M N : Type'} (t : type30 N) (s : type30 M) : ((term26 M N s t) = (term37 M N t s)) = (term36 M N t s).
Proof. exact (EQ_MP (@lem8033755 M N t s) (@lem8033742 M N t s)). Qed.
Lemma lem8033757 {M N : Type'} (t : type30 N) (s : type30 M) : (term36 M N t s) = ((term26 M N s t) = (term37 M N t s)).
Proof. exact (SYM (@lem8033756 M N t s)). Qed.
Lemma lem8033758 {N : Type'} (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : t = (@EMPTY (cart real N)).
Proof. exact (h1). Qed.
Lemma lem8033775 {N : Type'} (t : type30 N) (h1 : term40 N t) : term40 N t.
Proof. exact (h1). Qed.
Lemma lem8033798 {_141980 _141981 _141982 : Type'} : term41 _141980 _141981 _141982.
Proof. exact (proj1 (@lem8005965 _141980 _141981 _141982 Prop Prop Prop)). Qed.
Lemma lem8033799 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : term42 _141980 _141981 _141982 s.
Proof. exact (@lem8033798 _141980 _141981 _141982 s). Qed.
Lemma lem8033800 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : (term42 _141980 _141981 _141982 s) = ((@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982)))).
Proof. exact (eq_refl (term42 _141980 _141981 _141982 s)). Qed.
Lemma lem8033805 {N : Type'} (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : t = (@EMPTY (cart real N)).
Proof. exact (h1). Qed.
Lemma lem8033806 {M N : Type'} (s : type30 M) : (@PCROSS real M N s) = (@PCROSS real M N s).
Proof. exact (eq_refl (@PCROSS real M N s)). Qed.
Lemma lem8033807 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (@PCROSS real M N s t) = (@PCROSS real M N s (@EMPTY (cart real N))).
Proof. exact (MK_COMB (@lem8033806 M N s) (@lem8033805 N t h1)). Qed.
Lemma lem8033809 {_141980 _141981 _141982 : Type'} (s : type24 _141980 _141981) : (@PCROSS _141980 _141981 _141982 s (@EMPTY (cart _141980 _141982))) = (@EMPTY (cart _141980 (finite_sum _141981 _141982))).
Proof. exact (EQ_MP (@lem8033800 _141980 _141981 _141982 s) (@lem8033799 _141980 _141981 _141982 s)). Qed.
Lemma lem8033810 {M N : Type'} (s : type30 M) : (@PCROSS real M N s (@EMPTY (cart real N))) = (@EMPTY (cart real (finite_sum M N))).
Proof. exact (@lem8033809 real M N s). Qed.
Lemma lem8033811 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (@PCROSS real M N s t) = (@EMPTY (cart real (finite_sum M N))).
Proof. exact (TRANS (@lem8033807 M N s t h1) (@lem8033810 M N s)). Qed.
Lemma lem8033812 {M N : Type'} : (@IMAGE (cart real (finite_sum M N)) (cart real M) (@fstcart real M N)) = (@IMAGE (cart real (finite_sum M N)) (cart real M) (@fstcart real M N)).
Proof. exact (eq_refl (@IMAGE (cart real (finite_sum M N)) (cart real M) (@fstcart real M N))). Qed.
Lemma lem8033813 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (term26 M N s t) = (@IMAGE (cart real (finite_sum M N)) (cart real M) (@fstcart real M N) (@EMPTY (cart real (finite_sum M N)))).
Proof. exact (MK_COMB (@lem8033812 M N) (@lem8033811 M N s t h1)). Qed.
Lemma lem8033815 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem8033816 {M N : Type'} (f : type27 M N) : (@IMAGE (cart real (finite_sum M N)) (cart real M) f (@EMPTY (cart real (finite_sum M N)))) = (@EMPTY (cart real M)).
Proof. exact (@lem8033815 (type5 M N) (cart real M) f). Qed.
Lemma lem8033817 {M N : Type'} : (@IMAGE (cart real (finite_sum M N)) (cart real M) (@fstcart real M N) (@EMPTY (cart real (finite_sum M N)))) = (@EMPTY (cart real M)).
Proof. exact (@lem8033816 M N (@fstcart real M N)). Qed.
Lemma lem8033818 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (term26 M N s t) = (@EMPTY (cart real M)).
Proof. exact (TRANS (@lem8033813 M N s t h1) (@lem8033817 M N)). Qed.
Lemma lem8033819 {M : Type'} : (@eq ((cart real M) -> Prop)) = (@eq ((cart real M) -> Prop)).
Proof. exact (eq_refl (@eq ((cart real M) -> Prop))). Qed.
Lemma lem8033820 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (term43 M N s t) = (@eq ((cart real M) -> Prop) (@EMPTY (cart real M))).
Proof. exact (MK_COMB (@lem8033819 M) (@lem8033818 M N s t h1)). Qed.
Lemma lem8033821 {M : Type'} : (@EMPTY (cart real M)) = (@EMPTY (cart real M)).
Proof. exact (eq_refl (@EMPTY (cart real M))). Qed.
Lemma lem8033822 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : ((term26 M N s t) = (@EMPTY (cart real M))) = ((@EMPTY (cart real M)) = (@EMPTY (cart real M))).
Proof. exact (MK_COMB (@lem8033820 M N s t h1) (@lem8033821 M)). Qed.
Lemma lem8033824 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8033825 {M : Type'} (x : type30 M) : (x = x) = True.
Proof. exact (@lem8033824 (type30 M) x). Qed.
Lemma lem8033826 {M : Type'} : ((@EMPTY (cart real M)) = (@EMPTY (cart real M))) = True.
Proof. exact (@lem8033825 M (@EMPTY (cart real M))). Qed.
Lemma lem8033827 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : ((term26 M N s t) = (@EMPTY (cart real M))) = True.
Proof. exact (TRANS (@lem8033822 M N s t h1) (@lem8033826 M)). Qed.
Lemma lem8033828 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : True = ((term26 M N s t) = (@EMPTY (cart real M))).
Proof. exact (SYM (@lem8033827 M N s t h1)). Qed.
Lemma lem8033860 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem8033738 A s t) (@lem8033737 A s t)). Qed.
Lemma lem8033861 {M : Type'} (s : type30 M) (t : type30 M) : (s = t) = (term44 M s t).
Proof. exact (@lem8033860 (cart real M) s t). Qed.
Lemma lem8033862 {M N : Type'} (t : type30 N) (s : type30 M) : ((term26 M N s t) = s) = (term45 M N t s).
Proof. exact (@lem8033861 M (term26 M N s t) s). Qed.
Lemma lem8033872 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term12 A B y f s) = (term13 A B y f s).
Proof. exact (EQ_MP (@lem8033732 A B y f s) (@lem8033731 A B y s f)). Qed.
Lemma lem8033873 {M N : Type'} (y : cart real M) (f : type27 M N) (s : type29 M N) : (term46 M N y f s) = (term47 M N y f s).
Proof. exact (@lem8033872 (type5 M N) (cart real M) y f s). Qed.
Lemma lem8033874 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) : (term48 M N x s t) = (term49 M N x s t).
Proof. exact (@lem8033873 M N x (@fstcart real M N) (@PCROSS real M N s t)). Qed.
Lemma lem8033885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8033886 {M N : Type'} (x : cart real M) (s : type30 M) (t : type30 N) : (term50 M N x s t) = (term51 M N x s t).
Proof. exact (MK_COMB (@lem8033885) (@lem8033874 M N x s t)). Qed.
Lemma lem8033887 {M : Type'} (x : cart real M) (s : type30 M) : (@IN (cart real M) x s) = (@IN (cart real M) x s).
Proof. exact (eq_refl (@IN (cart real M) x s)). Qed.
Lemma lem8033888 {M N : Type'} (t : type30 N) (x : cart real M) (s : type30 M) : ((term48 M N x s t) = (@IN (cart real M) x s)) = ((term49 M N x s t) = (@IN (cart real M) x s)).
Proof. exact (MK_COMB (@lem8033886 M N x s t) (@lem8033887 M x s)). Qed.
Lemma lem8033893 {M N : Type'} (t : type30 N) (s : type30 M) : (term52 M N t s) = (term53 M N t s).
Proof. exact (fun_ext (fun x : cart real M => @lem8033888 M N t x s)). Qed.
Lemma lem8033894 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8033895 {M N : Type'} (t : type30 N) (s : type30 M) : (term45 M N t s) = (term54 M N t s).
Proof. exact (MK_COMB (@lem8033894 M) (@lem8033893 M N t s)). Qed.
Lemma lem8033900 {M N : Type'} (t : type30 N) (s : type30 M) : ((term26 M N s t) = s) = (term54 M N t s).
Proof. exact (TRANS (@lem8033862 M N t s) (@lem8033895 M N t s)). Qed.
Lemma lem8033901 {M N : Type'} (t : type30 N) (s : type30 M) : (term54 M N t s) = ((term26 M N s t) = s).
Proof. exact (SYM (@lem8033900 M N t s)). Qed.
Lemma lem8033915 (t2 : Prop) (t1 : Prop) : (t1 /\ t2) = (t2 /\ t1).
Proof. exact (EQ_MP (@lem8033723 t2 t1) (@lem8033722 t1 t2)). Qed.
Lemma lem8033916 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : type5 M N) : (term55 M N x x' s t) = (term56 M N s t x x').
Proof. exact (@lem8033915 (term57 M N x' s t) (x = (@fstcart real M N x'))). Qed.
Lemma lem8033917 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term58 M N x s t) = (term59 M N s t x).
Proof. exact (fun_ext (fun x' : type5 M N => @lem8033916 M N s t x x')). Qed.
Lemma lem8033918 {M N : Type'} : (@ex (cart real (finite_sum M N))) = (@ex (cart real (finite_sum M N))).
Proof. exact (eq_refl (@ex (cart real (finite_sum M N)))). Qed.
Lemma lem8033919 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term49 M N x s t) = (term60 M N s t x).
Proof. exact (MK_COMB (@lem8033918 M N) (@lem8033917 M N s t x)). Qed.
Lemma lem8033920 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8033921 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term51 M N x s t) = (term61 M N s t x).
Proof. exact (MK_COMB (@lem8033920) (@lem8033919 M N s t x)). Qed.
Lemma lem8033922 {M : Type'} (x : cart real M) (s : type30 M) : (@IN (cart real M) x s) = (@IN (cart real M) x s).
Proof. exact (eq_refl (@IN (cart real M) x s)). Qed.
Lemma lem8033923 {M N : Type'} (t : type30 N) (x : cart real M) (s : type30 M) : ((term49 M N x s t) = (@IN (cart real M) x s)) = ((term60 M N s t x) = (@IN (cart real M) x s)).
Proof. exact (MK_COMB (@lem8033921 M N s t x) (@lem8033922 M x s)). Qed.
Lemma lem8033924 {M N : Type'} (t : type30 N) (s : type30 M) : (term53 M N t s) = (term62 M N t s).
Proof. exact (fun_ext (fun x : cart real M => @lem8033923 M N t x s)). Qed.
Lemma lem8033925 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8033926 {M N : Type'} (t : type30 N) (s : type30 M) : (term54 M N t s) = (term63 M N t s).
Proof. exact (MK_COMB (@lem8033925 M) (@lem8033924 M N t s)). Qed.
Lemma lem8033927 {M N : Type'} (t : type30 N) (s : type30 M) : (term63 M N t s) = (term54 M N t s).
Proof. exact (SYM (@lem8033926 M N t s)). Qed.
Lemma lem8033935 {_141895 _141896 _141897 : Type'} (s : type24 _141895 _141896) (t : type24 _141895 _141897) (P : type16 _141895 _141896 _141897) : (term64 _141895 _141896 _141897 s t P) = (term65 _141895 _141896 _141897 s t P).
Proof. exact (EQ_MP (@lem8004099 _141895 _141896 _141897 s t P) (@lem0)). Qed.
Lemma lem8033936 {M N : Type'} (s : type30 M) (t : type30 N) (P : type29 M N) : (term66 M N s t P) = (term67 M N s t P).
Proof. exact (@lem8033935 real M N s t P). Qed.
Lemma lem8033937 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term68 M N s t x) = (term69 M N s t x).
Proof. exact (@lem8033936 M N s t (term70 M N x)). Qed.
Lemma lem8033938 {M N : Type'} (x : cart real M) (x' : type5 M N) : (term71 M N x x') = (x = (@fstcart real M N x')).
Proof. exact (eq_refl (term71 M N x x')). Qed.
Lemma lem8033939 {M N : Type'} (x : type5 M N) (s : type30 M) (t : type30 N) : (term72 M N x s t) = (term72 M N x s t).
Proof. exact (eq_refl (term72 M N x s t)). Qed.
Lemma lem8033940 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : type5 M N) : (term73 M N s t x x') = (term56 M N s t x x').
Proof. exact (MK_COMB (@lem8033939 M N x' s t) (@lem8033938 M N x x')). Qed.
Lemma lem8033941 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term74 M N s t x) = (term59 M N s t x).
Proof. exact (fun_ext (fun x' : type5 M N => @lem8033940 M N s t x x')). Qed.
Lemma lem8033942 {M N : Type'} : (@ex (cart real (finite_sum M N))) = (@ex (cart real (finite_sum M N))).
Proof. exact (eq_refl (@ex (cart real (finite_sum M N)))). Qed.
Lemma lem8033943 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term68 M N s t x) = (term60 M N s t x).
Proof. exact (MK_COMB (@lem8033942 M N) (@lem8033941 M N s t x)). Qed.
Lemma lem8033944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8033945 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term75 M N s t x) = (term61 M N s t x).
Proof. exact (MK_COMB (@lem8033944) (@lem8033943 M N s t x)). Qed.
Lemma lem8033946 {M N : Type'} (x : cart real M) (x' : cart real M) (y : cart real N) : (term76 M N x x' y) = (x = (term77 M N x' y)).
Proof. exact (eq_refl (term76 M N x x' y)). Qed.
Lemma lem8033947 {N : Type'} (y : cart real N) (t : type30 N) : (term78 N y t) = (term78 N y t).
Proof. exact (eq_refl (term78 N y t)). Qed.
Lemma lem8033948 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) (y : cart real N) : (term79 M N t x x' y) = (term80 M N t x x' y).
Proof. exact (MK_COMB (@lem8033947 N y t) (@lem8033946 M N x x' y)). Qed.
Lemma lem8033949 {M : Type'} (x' : cart real M) (s : type30 M) : (term78 M x' s) = (term78 M x' s).
Proof. exact (eq_refl (term78 M x' s)). Qed.
Lemma lem8033950 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) (y : cart real N) : (term81 M N s t x x' y) = (term82 M N s t x x' y).
Proof. exact (MK_COMB (@lem8033949 M x' s) (@lem8033948 M N t x x' y)). Qed.
Lemma lem8033951 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term83 M N s t x x') = (term84 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8033950 M N s t x x' y)). Qed.
Lemma lem8033952 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8033953 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term85 M N s t x x') = (term86 M N s t x x').
Proof. exact (MK_COMB (@lem8033952 N) (@lem8033951 M N s t x x')). Qed.
Lemma lem8033954 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term87 M N s t x) = (term88 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8033953 M N s t x x')). Qed.
Lemma lem8033955 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8033956 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term69 M N s t x) = (term89 M N s t x).
Proof. exact (MK_COMB (@lem8033955 M) (@lem8033954 M N s t x)). Qed.
Lemma lem8033957 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : ((term68 M N s t x) = (term69 M N s t x)) = ((term60 M N s t x) = (term89 M N s t x)).
Proof. exact (MK_COMB (@lem8033945 M N s t x) (@lem8033956 M N s t x)). Qed.
Lemma lem8033958 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term60 M N s t x) = (term89 M N s t x).
Proof. exact (EQ_MP (@lem8033957 M N s t x) (@lem8033937 M N s t x)). Qed.
Lemma lem8033974 {A M N : Type'} (y : cart A N) (x : cart A M) : (term3 A M N x y) = x.
Proof. exact (EQ_MP (@lem8033717 A M N y x) (@lem8033716 A M N x y)). Qed.
Lemma lem8033975 {M N : Type'} (y : cart real N) (x : cart real M) : (term77 M N x y) = x.
Proof. exact (@lem8033974 real M N y x). Qed.
Lemma lem8033976 {M N : Type'} (y : cart real N) (x' : cart real M) : (term77 M N x' y) = x'.
Proof. exact (@lem8033975 M N y x'). Qed.
Lemma lem8033977 {M : Type'} (x : cart real M) : (@eq (cart real M) x) = (@eq (cart real M) x).
Proof. exact (eq_refl (@eq (cart real M) x)). Qed.
Lemma lem8033978 {M N : Type'} (y : cart real N) (x : cart real M) (x' : cart real M) : (x = (term77 M N x' y)) = (x = x').
Proof. exact (MK_COMB (@lem8033977 M x) (@lem8033976 M N y x')). Qed.
Lemma lem8033981 {N : Type'} (y : cart real N) (t : type30 N) : (term78 N y t) = (term78 N y t).
Proof. exact (eq_refl (term78 N y t)). Qed.
Lemma lem8033982 {M N : Type'} (y : cart real N) (t : type30 N) (x : cart real M) (x' : cart real M) : (term80 M N t x x' y) = (term90 M N y t x x').
Proof. exact (MK_COMB (@lem8033981 N y t) (@lem8033978 M N y x x')). Qed.
Lemma lem8033985 {M : Type'} (x' : cart real M) (s : type30 M) : (term78 M x' s) = (term78 M x' s).
Proof. exact (eq_refl (term78 M x' s)). Qed.
Lemma lem8033986 {M N : Type'} (s : type30 M) (y : cart real N) (t : type30 N) (x : cart real M) (x' : cart real M) : (term82 M N s t x x' y) = (term91 M N s y t x x').
Proof. exact (MK_COMB (@lem8033985 M x' s) (@lem8033982 M N y t x x')). Qed.
Lemma lem8033989 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term84 M N s t x x') = (term92 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8033986 M N s y t x x')). Qed.
Lemma lem8033990 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8033991 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term86 M N s t x x') = (term93 M N s t x x').
Proof. exact (MK_COMB (@lem8033990 N) (@lem8033989 M N s t x x')). Qed.
Lemma lem8033996 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term88 M N s t x) = (term94 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8033991 M N s t x x')). Qed.
Lemma lem8033997 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8033998 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term89 M N s t x) = (term95 M N s t x).
Proof. exact (MK_COMB (@lem8033997 M) (@lem8033996 M N s t x)). Qed.
Lemma lem8034003 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term60 M N s t x) = (term95 M N s t x).
Proof. exact (TRANS (@lem8033958 M N s t x) (@lem8033998 M N s t x)). Qed.
Lemma lem8034004 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034005 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term61 M N s t x) = (term96 M N s t x).
Proof. exact (MK_COMB (@lem8034004) (@lem8034003 M N s t x)). Qed.
Lemma lem8034006 {M : Type'} (x : cart real M) (s : type30 M) : (@IN (cart real M) x s) = (@IN (cart real M) x s).
Proof. exact (eq_refl (@IN (cart real M) x s)). Qed.
Lemma lem8034007 {M N : Type'} (t : type30 N) (x : cart real M) (s : type30 M) : ((term60 M N s t x) = (@IN (cart real M) x s)) = ((term95 M N s t x) = (@IN (cart real M) x s)).
Proof. exact (MK_COMB (@lem8034005 M N s t x) (@lem8034006 M x s)). Qed.
Lemma lem8034010 {M N : Type'} (t : type30 N) (s : type30 M) : (term62 M N t s) = (term97 M N t s).
Proof. exact (fun_ext (fun x : cart real M => @lem8034007 M N t x s)). Qed.
Lemma lem8034011 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034012 {M N : Type'} (t : type30 N) (s : type30 M) : (term63 M N t s) = (term98 M N t s).
Proof. exact (MK_COMB (@lem8034011 M) (@lem8034010 M N t s)). Qed.
Lemma lem8034017 {M N : Type'} (t : type30 N) (s : type30 M) : (term98 M N t s) = (term63 M N t s).
Proof. exact (SYM (@lem8034012 M N t s)). Qed.
Lemma lem8034033 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term17 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8034034 {N : Type'} (s : type30 N) (t : type30 N) : (s = t) = (term44 N s t).
Proof. exact (@lem8034033 (cart real N) s t). Qed.
Lemma lem8034035 {N : Type'} (t : type30 N) : (t = (@EMPTY (cart real N))) = (term99 N t).
Proof. exact (@lem8034034 N t (@EMPTY (cart real N))). Qed.
Lemma lem8034044 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8034045 {N : Type'} (t : type30 N) : (term40 N t) = (term100 N t).
Proof. exact (MK_COMB (@lem8034044) (@lem8034035 N t)). Qed.
Lemma lem8034046 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8034047 {N : Type'} (t : type30 N) : (term27 N t) = (term101 N t).
Proof. exact (MK_COMB (@lem8034046) (@lem8034045 N t)). Qed.
Lemma lem8034072 {M N : Type'} (t : type30 N) (s : type30 M) : (term98 M N t s) = (term98 M N t s).
Proof. exact (eq_refl (term98 M N t s)). Qed.
Lemma lem8034073 {M N : Type'} (t : type30 N) (s : type30 M) : (term102 M N t s) = (term103 M N t s).
Proof. exact (MK_COMB (@lem8034047 N t) (@lem8034072 M N t s)). Qed.
Lemma lem8034076 {M N : Type'} (t : type30 N) (s : type30 M) : (term103 M N t s) = (term102 M N t s).
Proof. exact (SYM (@lem8034073 M N t s)). Qed.
Lemma lem8034086 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8034087 {N : Type'} (P : type30 N) (x : cart real N) : (@IN (cart real N) x P) = (P x).
Proof. exact (@lem8034086 (cart real N) P x). Qed.
Lemma lem8034088 {N : Type'} (t : type30 N) (x : cart real N) : (@IN (cart real N) x t) = (t x).
Proof. exact (@lem8034087 N t x). Qed.
Lemma lem8034089 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034090 {N : Type'} (t : type30 N) (x : cart real N) : (term104 N x t) = (term105 N t x).
Proof. exact (MK_COMB (@lem8034089) (@lem8034088 N t x)). Qed.
Lemma lem8034092 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8034093 {N : Type'} (x : cart real N) : (@IN (cart real N) x (@EMPTY (cart real N))) = False.
Proof. exact (@lem8034092 (cart real N) x). Qed.
Lemma lem8034094 {N : Type'} (t : type30 N) (x : cart real N) : ((@IN (cart real N) x t) = (@IN (cart real N) x (@EMPTY (cart real N)))) = ((t x) = False).
Proof. exact (MK_COMB (@lem8034090 N t x) (@lem8034093 N x)). Qed.
Lemma lem8034096 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8034097 {N : Type'} (t : type30 N) (x : cart real N) : ((t x) = False) = (term106 N t x).
Proof. exact (@lem8034096 (t x)). Qed.
Lemma lem8034098 {N : Type'} (t : type30 N) (x : cart real N) : ((@IN (cart real N) x t) = (@IN (cart real N) x (@EMPTY (cart real N)))) = (term106 N t x).
Proof. exact (TRANS (@lem8034094 N t x) (@lem8034097 N t x)). Qed.
Lemma lem8034099 {N : Type'} (t : type30 N) : (term107 N t) = (term108 N t).
Proof. exact (fun_ext (fun x : cart real N => @lem8034098 N t x)). Qed.
Lemma lem8034100 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034101 {N : Type'} (t : type30 N) : (term99 N t) = (term109 N t).
Proof. exact (MK_COMB (@lem8034100 N) (@lem8034099 N t)). Qed.
Lemma lem8034106 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8034107 {N : Type'} (t : type30 N) : (term100 N t) = (term110 N t).
Proof. exact (MK_COMB (@lem8034106) (@lem8034101 N t)). Qed.
Lemma lem8034108 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8034109 {N : Type'} (t : type30 N) : (term101 N t) = (term111 N t).
Proof. exact (MK_COMB (@lem8034108) (@lem8034107 N t)). Qed.
Lemma lem8034127 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8034128 {M : Type'} (P : type30 M) (x : cart real M) : (@IN (cart real M) x P) = (P x).
Proof. exact (@lem8034127 (cart real M) P x). Qed.
Lemma lem8034129 {M : Type'} (s : type30 M) (x' : cart real M) : (@IN (cart real M) x' s) = (s x').
Proof. exact (@lem8034128 M s x'). Qed.
Lemma lem8034130 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034131 {M : Type'} (s : type30 M) (x' : cart real M) : (term78 M x' s) = (term112 M s x').
Proof. exact (MK_COMB (@lem8034130) (@lem8034129 M s x')). Qed.
Lemma lem8034135 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8034136 {N : Type'} (P : type30 N) (x : cart real N) : (@IN (cart real N) x P) = (P x).
Proof. exact (@lem8034135 (cart real N) P x). Qed.
Lemma lem8034137 {N : Type'} (t : type30 N) (y : cart real N) : (@IN (cart real N) y t) = (t y).
Proof. exact (@lem8034136 N t y). Qed.
Lemma lem8034138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034139 {N : Type'} (t : type30 N) (y : cart real N) : (term78 N y t) = (term112 N t y).
Proof. exact (MK_COMB (@lem8034138) (@lem8034137 N t y)). Qed.
Lemma lem8034142 {M : Type'} (x : cart real M) (x' : cart real M) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem8034143 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term90 M N y t x x') = (term113 M N t y x x').
Proof. exact (MK_COMB (@lem8034139 N t y) (@lem8034142 M x x')). Qed.
Lemma lem8034146 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term91 M N s y t x x') = (term114 M N s t y x x').
Proof. exact (MK_COMB (@lem8034131 M s x') (@lem8034143 M N t y x x')). Qed.
Lemma lem8034149 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term92 M N s t x x') = (term115 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034146 M N s t y x x')). Qed.
Lemma lem8034150 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034151 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term93 M N s t x x') = (term116 M N s t x x').
Proof. exact (MK_COMB (@lem8034150 N) (@lem8034149 M N s t x x')). Qed.
Lemma lem8034156 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term94 M N s t x) = (term117 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034151 M N s t x x')). Qed.
Lemma lem8034157 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034158 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term95 M N s t x) = (term118 M N s t x).
Proof. exact (MK_COMB (@lem8034157 M) (@lem8034156 M N s t x)). Qed.
Lemma lem8034163 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034164 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term96 M N s t x) = (term119 M N s t x).
Proof. exact (MK_COMB (@lem8034163) (@lem8034158 M N s t x)). Qed.
Lemma lem8034166 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8034167 {M : Type'} (P : type30 M) (x : cart real M) : (@IN (cart real M) x P) = (P x).
Proof. exact (@lem8034166 (cart real M) P x). Qed.
Lemma lem8034168 {M : Type'} (s : type30 M) (x : cart real M) : (@IN (cart real M) x s) = (s x).
Proof. exact (@lem8034167 M s x). Qed.
Lemma lem8034169 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : ((term95 M N s t x) = (@IN (cart real M) x s)) = ((term118 M N s t x) = (s x)).
Proof. exact (MK_COMB (@lem8034164 M N s t x) (@lem8034168 M s x)). Qed.
Lemma lem8034172 {M N : Type'} (t : type30 N) (s : type30 M) : (term97 M N t s) = (term120 M N t s).
Proof. exact (fun_ext (fun x : cart real M => @lem8034169 M N t s x)). Qed.
Lemma lem8034173 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034174 {M N : Type'} (t : type30 N) (s : type30 M) : (term98 M N t s) = (term121 M N t s).
Proof. exact (MK_COMB (@lem8034173 M) (@lem8034172 M N t s)). Qed.
Lemma lem8034179 {M N : Type'} (t : type30 N) (s : type30 M) : (term103 M N t s) = (term122 M N t s).
Proof. exact (MK_COMB (@lem8034109 N t) (@lem8034174 M N t s)). Qed.
Lemma lem8034182 {M N : Type'} (t : type30 N) (s : type30 M) : (term122 M N t s) = (term103 M N t s).
Proof. exact (SYM (@lem8034179 M N t s)). Qed.
Lemma lem8034184 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8034185 {M N : Type'} (t : type30 N) (s : type30 M) : (term122 M N t s) = (term124 M N t s).
Proof. exact (@lem8034184 (term122 M N t s)). Qed.
Lemma lem8034186 {M N : Type'} (t : type30 N) (s : type30 M) : (term124 M N t s) = (term122 M N t s).
Proof. exact (SYM (@lem8034185 M N t s)). Qed.
Lemma lem8034187 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term125 M N t s) : term125 M N t s.
Proof. exact (h1). Qed.
Lemma lem8034190 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term124 M N t s) : term124 M N t s.
Proof. exact (h1). Qed.
Lemma lem8034191 {M N : Type'} (t : type30 N) (s : type30 M) : term126 M N t s.
Proof. exact (fun h0 : term124 M N t s => @lem8034190 M N t s h0). Qed.
Lemma lem8034192 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term126 M N t s) : term126 M N t s.
Proof. exact (h1). Qed.
Lemma lem8034193 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term124 M N t s) : term124 M N t s.
Proof. exact (h1). Qed.
Lemma lem8034194 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term124 M N t s) (h2 : term126 M N t s) : term124 M N t s.
Proof. exact (@lem8034192 M N t s h2 (@lem8034193 M N t s h1)). Qed.
Lemma lem8034195 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term124 M N t s) : term127 M N t s.
Proof. exact (fun h0 : term126 M N t s => @lem8034194 M N t s h1 h0). Qed.
Lemma lem8034196 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term126 M N t s) : term126 M N t s.
Proof. exact (h1). Qed.
Lemma lem8034197 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term124 M N t s) (h2 : term126 M N t s) : term124 M N t s.
Proof. exact (@lem8034195 M N t s h1 (@lem8034196 M N t s h2)). Qed.
Lemma lem8034198 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term126 M N t s) : term126 M N t s.
Proof. exact (fun h0 : term124 M N t s => @lem8034197 M N t s h0 h1). Qed.
Lemma lem8034199 {M N : Type'} (t : type30 N) (s : type30 M) : term128 M N t s.
Proof. exact (fun h0 : term126 M N t s => @lem8034198 M N t s h0). Qed.
Lemma lem8034202 {M N : Type'} (t : type30 N) (s : type30 M) : term126 M N t s.
Proof. exact (@lem8034199 M N t s (@lem8034191 M N t s)). Qed.
Lemma lem8034203 {M N : Type'} (t : type30 N) (s : type30 M) : term126 M N t s.
Proof. exact (@lem8034202 M N t s). Qed.
Lemma lem8034213 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem8034214 {M N : Type'} (t : type30 N) (s : type30 M) : (term124 M N t s) = (term129 M N t s).
Proof. exact (@lem8034213 (term125 M N t s)). Qed.
Lemma lem8034216 (t : Prop) : (term130 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem8034217 {M N : Type'} (t : type30 N) (s : type30 M) : (term129 M N t s) = (term122 M N t s).
Proof. exact (@lem8034216 (term122 M N t s)). Qed.
Lemma lem8034220 {M N : Type'} (t : type30 N) (s : type30 M) : (term124 M N t s) = (term122 M N t s).
Proof. exact (TRANS (@lem8034214 M N t s) (@lem8034217 M N t s)). Qed.
Lemma lem8034234 {A : Type'} (P : Prop) (Q : A -> Prop) : (term131 A P Q) = (term132 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem8034235 {N : Type'} (P : Prop) (Q : type30 N) : (term133 N P Q) = (term134 N P Q).
Proof. exact (@lem8034234 (cart real N) P Q). Qed.
Lemma lem8034236 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term135 M N s t x x') = (term136 M N s t x x').
Proof. exact (@lem8034235 N (s x') (term137 M N t x x')). Qed.
Lemma lem8034237 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term138 M N t x x' y) = (term113 M N t y x x').
Proof. exact (eq_refl (term138 M N t x x' y)). Qed.
Lemma lem8034238 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034239 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term139 M N s t x x' y) = (term114 M N s t y x x').
Proof. exact (MK_COMB (@lem8034238 M s x') (@lem8034237 M N t y x x')). Qed.
Lemma lem8034240 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term140 M N s t x x') = (term115 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034239 M N s t y x x')). Qed.
Lemma lem8034241 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034242 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term135 M N s t x x') = (term116 M N s t x x').
Proof. exact (MK_COMB (@lem8034241 N) (@lem8034240 M N s t x x')). Qed.
Lemma lem8034243 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034244 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term141 M N s t x x') = (term142 M N s t x x').
Proof. exact (MK_COMB (@lem8034243) (@lem8034242 M N s t x x')). Qed.
Lemma lem8034245 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term138 M N t x x' y) = (term113 M N t y x x').
Proof. exact (eq_refl (term138 M N t x x' y)). Qed.
Lemma lem8034246 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term143 M N t x x') = (term137 M N t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034245 M N t y x x')). Qed.
Lemma lem8034247 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034248 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term144 M N t x x') = (term145 M N t x x').
Proof. exact (MK_COMB (@lem8034247 N) (@lem8034246 M N t x x')). Qed.
Lemma lem8034249 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034250 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term136 M N s t x x') = (term146 M N s t x x').
Proof. exact (MK_COMB (@lem8034249 M s x') (@lem8034248 M N t x x')). Qed.
Lemma lem8034251 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : ((term135 M N s t x x') = (term136 M N s t x x')) = ((term116 M N s t x x') = (term146 M N s t x x')).
Proof. exact (MK_COMB (@lem8034244 M N s t x x') (@lem8034250 M N s t x x')). Qed.
Lemma lem8034252 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term116 M N s t x x') = (term146 M N s t x x').
Proof. exact (EQ_MP (@lem8034251 M N s t x x') (@lem8034236 M N s t x x')). Qed.
Lemma lem8034276 {A : Type'} (P : A -> Prop) (Q : Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem16440 A P Q) (@lem16439 A P Q)). Qed.
Lemma lem8034277 {N : Type'} (P : type30 N) (Q : Prop) : (term149 N P Q) = (term150 N P Q).
Proof. exact (@lem8034276 (cart real N) P Q). Qed.
Lemma lem8034278 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term145 M N t x x') = (term151 M N t x x').
Proof. exact (@lem8034277 N t (x = x')). Qed.
Lemma lem8034285 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034286 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term146 M N s t x x') = (term152 M N s t x x').
Proof. exact (MK_COMB (@lem8034285 M s x') (@lem8034278 M N t x x')). Qed.
Lemma lem8034289 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term116 M N s t x x') = (term152 M N s t x x').
Proof. exact (TRANS (@lem8034252 M N s t x x') (@lem8034286 M N s t x x')). Qed.
Lemma lem8034290 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term117 M N s t x) = (term153 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034289 M N s t x x')). Qed.
Lemma lem8034291 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034292 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term118 M N s t x) = (term154 M N s t x).
Proof. exact (MK_COMB (@lem8034291 M) (@lem8034290 M N s t x)). Qed.
Lemma lem8034321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034322 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term119 M N s t x) = (term155 M N s t x).
Proof. exact (MK_COMB (@lem8034321) (@lem8034292 M N s t x)). Qed.
Lemma lem8034323 {M : Type'} (s : type30 M) (x : cart real M) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8034324 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : ((term118 M N s t x) = (s x)) = ((term154 M N s t x) = (s x)).
Proof. exact (MK_COMB (@lem8034322 M N s t x) (@lem8034323 M s x)). Qed.
Lemma lem8034325 {M N : Type'} (t : type30 N) (s : type30 M) : (term120 M N t s) = (term156 M N t s).
Proof. exact (fun_ext (fun x : cart real M => @lem8034324 M N t s x)). Qed.
Lemma lem8034326 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034327 {M N : Type'} (t : type30 N) (s : type30 M) : (term121 M N t s) = (term157 M N t s).
Proof. exact (MK_COMB (@lem8034326 M) (@lem8034325 M N t s)). Qed.
Lemma lem8034332 {N : Type'} (t : type30 N) : (term111 N t) = (term111 N t).
Proof. exact (eq_refl (term111 N t)). Qed.
Lemma lem8034333 {M N : Type'} (t : type30 N) (s : type30 M) : (term122 M N t s) = (term158 M N t s).
Proof. exact (MK_COMB (@lem8034332 N t) (@lem8034327 M N t s)). Qed.
Lemma lem8034336 {M N : Type'} (t : type30 N) (s : type30 M) : (term124 M N t s) = (term158 M N t s).
Proof. exact (TRANS (@lem8034220 M N t s) (@lem8034333 M N t s)). Qed.
Lemma lem8034337 {M N : Type'} (s : type30 M) : (term159 M N s) = (term160 M N s).
Proof. exact (fun_ext (fun t : type30 N => @lem8034336 M N t s)). Qed.
Lemma lem8034338 {N : Type'} : (@all ((cart real N) -> Prop)) = (@all ((cart real N) -> Prop)).
Proof. exact (eq_refl (@all ((cart real N) -> Prop))). Qed.
Lemma lem8034339 {M N : Type'} (s : type30 M) : (term161 M N s) = (term162 M N s).
Proof. exact (MK_COMB (@lem8034338 N) (@lem8034337 M N s)). Qed.
Lemma lem8034344 {M N : Type'} : (term163 M N) = (term164 M N).
Proof. exact (fun_ext (fun s : type30 M => @lem8034339 M N s)). Qed.
Lemma lem8034345 {M : Type'} : (@all ((cart real M) -> Prop)) = (@all ((cart real M) -> Prop)).
Proof. exact (eq_refl (@all ((cart real M) -> Prop))). Qed.
Lemma lem8034354 {M N : Type'} : (term165 M N) = (term166 M N).
Proof. exact (MK_COMB (@lem8034345 M) (@lem8034344 M N)). Qed.
Lemma lem8034355 {M : Type'} (s : type30 M) (x : cart real M) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8034356 {M : Type'} (x : cart real M) (x' : cart real M) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem8034357 {N : Type'} (t : type30 N) (y : cart real N) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem8034358 {N : Type'} (t : type30 N) : (term167 N t) = (term167 N t).
Proof. exact (fun_ext (fun y : cart real N => @lem8034357 N t y)). Qed.
Lemma lem8034359 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034360 {N : Type'} (t : type30 N) : (term168 N t) = (term168 N t).
Proof. exact (MK_COMB (@lem8034359 N) (@lem8034358 N t)). Qed.
Lemma lem8034361 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034362 {N : Type'} (t : type30 N) : (term169 N t) = (term169 N t).
Proof. exact (MK_COMB (@lem8034361) (@lem8034360 N t)). Qed.
Lemma lem8034363 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term151 M N t x x') = (term151 M N t x x').
Proof. exact (MK_COMB (@lem8034362 N t) (@lem8034356 M x x')). Qed.
Lemma lem8034366 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034367 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term152 M N s t x x') = (term152 M N s t x x').
Proof. exact (MK_COMB (@lem8034366 M s x') (@lem8034363 M N t x x')). Qed.
Lemma lem8034368 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term153 M N s t x) = (term153 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034367 M N s t x x')). Qed.
Lemma lem8034369 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034370 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term154 M N s t x) = (term154 M N s t x).
Proof. exact (MK_COMB (@lem8034369 M) (@lem8034368 M N s t x)). Qed.
Lemma lem8034371 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034372 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term155 M N s t x) = (term155 M N s t x).
Proof. exact (MK_COMB (@lem8034371) (@lem8034370 M N s t x)). Qed.
Lemma lem8034373 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : ((term154 M N s t x) = (s x)) = ((term154 M N s t x) = (s x)).
Proof. exact (MK_COMB (@lem8034372 M N s t x) (@lem8034355 M s x)). Qed.
Lemma lem8034374 {M N : Type'} (t : type30 N) (s : type30 M) : (term156 M N t s) = (term156 M N t s).
Proof. exact (fun_ext (fun x : cart real M => @lem8034373 M N t s x)). Qed.
Lemma lem8034375 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034376 {M N : Type'} (t : type30 N) (s : type30 M) : (term157 M N t s) = (term157 M N t s).
Proof. exact (MK_COMB (@lem8034375 M) (@lem8034374 M N t s)). Qed.
Lemma lem8034379 {N : Type'} (t : type30 N) (x : cart real N) : (term106 N t x) = (term106 N t x).
Proof. exact (eq_refl (term106 N t x)). Qed.
Lemma lem8034380 {N : Type'} (t : type30 N) : (term108 N t) = (term108 N t).
Proof. exact (fun_ext (fun x : cart real N => @lem8034379 N t x)). Qed.
Lemma lem8034381 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034382 {N : Type'} (t : type30 N) : (term109 N t) = (term109 N t).
Proof. exact (MK_COMB (@lem8034381 N) (@lem8034380 N t)). Qed.
Lemma lem8034383 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8034384 {N : Type'} (t : type30 N) : (term110 N t) = (term110 N t).
Proof. exact (MK_COMB (@lem8034383) (@lem8034382 N t)). Qed.
Lemma lem8034385 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8034386 {N : Type'} (t : type30 N) : (term111 N t) = (term111 N t).
Proof. exact (MK_COMB (@lem8034385) (@lem8034384 N t)). Qed.
Lemma lem8034387 {M N : Type'} (t : type30 N) (s : type30 M) : (term158 M N t s) = (term158 M N t s).
Proof. exact (MK_COMB (@lem8034386 N t) (@lem8034376 M N t s)). Qed.
Lemma lem8034388 {M N : Type'} (s : type30 M) : (term160 M N s) = (term160 M N s).
Proof. exact (fun_ext (fun t : type30 N => @lem8034387 M N t s)). Qed.
Lemma lem8034389 {N : Type'} : (@all ((cart real N) -> Prop)) = (@all ((cart real N) -> Prop)).
Proof. exact (eq_refl (@all ((cart real N) -> Prop))). Qed.
Lemma lem8034390 {M N : Type'} (s : type30 M) : (term162 M N s) = (term162 M N s).
Proof. exact (MK_COMB (@lem8034389 N) (@lem8034388 M N s)). Qed.
Lemma lem8034391 {M N : Type'} : (term164 M N) = (term164 M N).
Proof. exact (fun_ext (fun s : type30 M => @lem8034390 M N s)). Qed.
Lemma lem8034392 {M : Type'} : (@all ((cart real M) -> Prop)) = (@all ((cart real M) -> Prop)).
Proof. exact (eq_refl (@all ((cart real M) -> Prop))). Qed.
Lemma lem8034393 {M N : Type'} : (term166 M N) = (term166 M N).
Proof. exact (MK_COMB (@lem8034392 M) (@lem8034391 M N)). Qed.
Lemma lem8034438 {M N : Type'} : (term165 M N) = (term166 M N).
Proof. exact (TRANS (@lem8034354 M N) (@lem8034393 M N)). Qed.
Lemma lem8034439 {M N : Type'} : (term166 M N) = (term165 M N).
Proof. exact (SYM (@lem8034438 M N)). Qed.
Lemma lem8034440 {N : Type'} (t : type30 N) (h1 : term110 N t) : term110 N t.
Proof. exact (h1). Qed.
Lemma lem8034442 (p : Prop) : p = (term123 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem8034443 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : ((term154 M N s t x) = (s x)) = (term170 M N t s x).
Proof. exact (@lem8034442 ((term154 M N s t x) = (s x))). Qed.
Lemma lem8034444 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term170 M N t s x) = ((term154 M N s t x) = (s x)).
Proof. exact (SYM (@lem8034443 M N t s x)). Qed.
Lemma lem8034445 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term171 M N t s x) : term171 M N t s x.
Proof. exact (h1). Qed.
Lemma lem8034448 {N : Type'} (t : type30 N) (x : cart real N) : (term172 N t x) = (t x).
Proof. exact (@lem16933 (t x)). Qed.
Lemma lem8034449 {N : Type'} (P : type30 N) : (term173 N P) = (term174 N P).
Proof. exact (@lem18392 (cart real N) P). Qed.
Lemma lem8034450 {N : Type'} (t : type30 N) : (term110 N t) = (term175 N t).
Proof. exact (@lem8034449 N (term108 N t)). Qed.
Lemma lem8034451 {N : Type'} (t : type30 N) (x : cart real N) : (term176 N t x) = (term106 N t x).
Proof. exact (eq_refl (term176 N t x)). Qed.
Lemma lem8034452 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8034453 {N : Type'} (t : type30 N) (x : cart real N) : (term177 N t x) = (term172 N t x).
Proof. exact (MK_COMB (@lem8034452) (@lem8034451 N t x)). Qed.
Lemma lem8034454 {N : Type'} (t : type30 N) (x : cart real N) : (term177 N t x) = (t x).
Proof. exact (TRANS (@lem8034453 N t x) (@lem8034448 N t x)). Qed.
Lemma lem8034455 {N : Type'} (t : type30 N) : (term178 N t) = (term167 N t).
Proof. exact (fun_ext (fun x : cart real N => @lem8034454 N t x)). Qed.
Lemma lem8034456 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034457 {N : Type'} (t : type30 N) : (term175 N t) = (term168 N t).
Proof. exact (MK_COMB (@lem8034456 N) (@lem8034455 N t)). Qed.
Lemma lem8034466 {N : Type'} (t : type30 N) : (term110 N t) = (term168 N t).
Proof. exact (TRANS (@lem8034450 N t) (@lem8034457 N t)). Qed.
Lemma lem8034467 {N : Type'} (t : type30 N) (h1 : term110 N t) : term168 N t.
Proof. exact (EQ_MP (@lem8034466 N t) (@lem8034440 N t h1)). Qed.
Lemma lem8034471 {N : Type'} (t : type30 N) (y : cart real N) : (t y) = (t y).
Proof. exact (eq_refl (t y)). Qed.
Lemma lem8034472 {N : Type'} (P : type30 N) : (term179 N P) = (term109 N P).
Proof. exact (@lem18394 (cart real N) P). Qed.
Lemma lem8034473 {N : Type'} (t : type30 N) : (term180 N t) = (term181 N t).
Proof. exact (@lem8034472 N (term167 N t)). Qed.
Lemma lem8034474 {N : Type'} (t : type30 N) (y : cart real N) : (term182 N t y) = (t y).
Proof. exact (eq_refl (term182 N t y)). Qed.
Lemma lem8034475 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8034477 {N : Type'} (t : type30 N) (y : cart real N) : (term183 N t y) = (term106 N t y).
Proof. exact (MK_COMB (@lem8034475) (@lem8034474 N t y)). Qed.
Lemma lem8034478 {N : Type'} (t : type30 N) : (term184 N t) = (term108 N t).
Proof. exact (fun_ext (fun y : cart real N => @lem8034477 N t y)). Qed.
Lemma lem8034479 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034480 {N : Type'} (t : type30 N) : (term181 N t) = (term109 N t).
Proof. exact (MK_COMB (@lem8034479 N) (@lem8034478 N t)). Qed.
Lemma lem8034481 {N : Type'} (t : type30 N) : (term180 N t) = (term109 N t).
Proof. exact (TRANS (@lem8034473 N t) (@lem8034480 N t)). Qed.
Lemma lem8034482 {N : Type'} (t : type30 N) : (term167 N t) = (term167 N t).
Proof. exact (fun_ext (fun y : cart real N => @lem8034471 N t y)). Qed.
Lemma lem8034483 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034484 {N : Type'} (t : type30 N) : (term168 N t) = (term168 N t).
Proof. exact (MK_COMB (@lem8034483 N) (@lem8034482 N t)). Qed.
Lemma lem8034485 {M : Type'} (x : cart real M) (x' : cart real M) : (term185 M x x') = (term185 M x x').
Proof. exact (eq_refl (term185 M x x')). Qed.
Lemma lem8034486 {M : Type'} (x : cart real M) (x' : cart real M) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem8034487 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034488 {N : Type'} (t : type30 N) : (term186 N t) = (term187 N t).
Proof. exact (MK_COMB (@lem8034487) (@lem8034481 N t)). Qed.
Lemma lem8034489 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term188 M N t x x') = (term189 M N t x x').
Proof. exact (MK_COMB (@lem8034488 N t) (@lem8034485 M x x')). Qed.
Lemma lem8034490 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term190 M N t x x') = (term188 M N t x x').
Proof. exact (@lem17045 (term168 N t) (x = x')). Qed.
Lemma lem8034491 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term190 M N t x x') = (term189 M N t x x').
Proof. exact (TRANS (@lem8034490 M N t x x') (@lem8034489 M N t x x')). Qed.
Lemma lem8034492 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034493 {N : Type'} (t : type30 N) : (term169 N t) = (term169 N t).
Proof. exact (MK_COMB (@lem8034492) (@lem8034484 N t)). Qed.
Lemma lem8034494 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term151 M N t x x') = (term151 M N t x x').
Proof. exact (MK_COMB (@lem8034493 N t) (@lem8034486 M x x')). Qed.
Lemma lem8034496 {M : Type'} (s : type30 M) (x' : cart real M) : (term191 M s x') = (term191 M s x').
Proof. exact (eq_refl (term191 M s x')). Qed.
Lemma lem8034497 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term192 M N s t x x') = (term193 M N s t x x').
Proof. exact (MK_COMB (@lem8034496 M s x') (@lem8034491 M N t x x')). Qed.
Lemma lem8034498 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term194 M N s t x x') = (term192 M N s t x x').
Proof. exact (@lem17045 (s x') (term151 M N t x x')). Qed.
Lemma lem8034499 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term194 M N s t x x') = (term193 M N s t x x').
Proof. exact (TRANS (@lem8034498 M N s t x x') (@lem8034497 M N s t x x')). Qed.
Lemma lem8034501 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034502 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term152 M N s t x x') = (term152 M N s t x x').
Proof. exact (MK_COMB (@lem8034501 M s x') (@lem8034494 M N t x x')). Qed.
Lemma lem8034503 {M : Type'} (P : type30 M) : (term179 M P) = (term109 M P).
Proof. exact (@lem18394 (cart real M) P). Qed.
Lemma lem8034504 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term195 M N s t x) = (term196 M N s t x).
Proof. exact (@lem8034503 M (term153 M N s t x)). Qed.
Lemma lem8034505 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term197 M N s t x x') = (term152 M N s t x x').
Proof. exact (eq_refl (term197 M N s t x x')). Qed.
Lemma lem8034506 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem8034507 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term198 M N s t x x') = (term194 M N s t x x').
Proof. exact (MK_COMB (@lem8034506) (@lem8034505 M N s t x x')). Qed.
Lemma lem8034508 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term198 M N s t x x') = (term193 M N s t x x').
Proof. exact (TRANS (@lem8034507 M N s t x x') (@lem8034499 M N s t x x')). Qed.
Lemma lem8034509 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term199 M N s t x) = (term200 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034508 M N s t x x')). Qed.
Lemma lem8034510 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034511 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term196 M N s t x) = (term201 M N s t x).
Proof. exact (MK_COMB (@lem8034510 M) (@lem8034509 M N s t x)). Qed.
Lemma lem8034512 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term195 M N s t x) = (term201 M N s t x).
Proof. exact (TRANS (@lem8034504 M N s t x) (@lem8034511 M N s t x)). Qed.
Lemma lem8034513 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term153 M N s t x) = (term153 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034502 M N s t x x')). Qed.
Lemma lem8034514 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034515 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term154 M N s t x) = (term154 M N s t x).
Proof. exact (MK_COMB (@lem8034514 M) (@lem8034513 M N s t x)). Qed.
Lemma lem8034516 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8034517 {M : Type'} (s : type30 M) (x : cart real M) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8034518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034519 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term202 M N s t x) = (term203 M N s t x).
Proof. exact (MK_COMB (@lem8034518) (@lem8034512 M N s t x)). Qed.
Lemma lem8034520 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term204 M N t s x) = (term205 M N t s x).
Proof. exact (MK_COMB (@lem8034519 M N s t x) (@lem8034517 M s x)). Qed.
Lemma lem8034521 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034522 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term206 M N s t x) = (term206 M N s t x).
Proof. exact (MK_COMB (@lem8034521) (@lem8034515 M N s t x)). Qed.
Lemma lem8034523 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term207 M N t s x) = (term207 M N t s x).
Proof. exact (MK_COMB (@lem8034522 M N s t x) (@lem8034516 M s x)). Qed.
Lemma lem8034524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034525 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term208 M N t s x) = (term208 M N t s x).
Proof. exact (MK_COMB (@lem8034524) (@lem8034523 M N t s x)). Qed.
Lemma lem8034526 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term209 M N t s x) = (term210 M N t s x).
Proof. exact (MK_COMB (@lem8034525 M N t s x) (@lem8034520 M N t s x)). Qed.
Lemma lem8034527 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term171 M N t s x) = (term209 M N t s x).
Proof. exact (@lem17646 (term154 M N s t x) (s x)). Qed.
Lemma lem8034528 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term171 M N t s x) = (term210 M N t s x).
Proof. exact (TRANS (@lem8034527 M N t s x) (@lem8034526 M N t s x)). Qed.
Lemma lem8034615 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8034616 {N : Type'} (P : type30 N) (Q : Prop) : (term150 N P Q) = (term149 N P Q).
Proof. exact (@lem8034615 (cart real N) P Q). Qed.
Lemma lem8034617 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term151 M N t x x') = (term145 M N t x x').
Proof. exact (@lem8034616 N t (x = x')). Qed.
Lemma lem8034618 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034619 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term152 M N s t x x') = (term146 M N s t x x').
Proof. exact (MK_COMB (@lem8034618 M s x') (@lem8034617 M N t x x')). Qed.
Lemma lem8034621 {A : Type'} (P : Prop) (Q : A -> Prop) : (term132 A P Q) = (term131 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem8034622 {N : Type'} (P : Prop) (Q : type30 N) : (term134 N P Q) = (term133 N P Q).
Proof. exact (@lem8034621 (cart real N) P Q). Qed.
Lemma lem8034623 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term136 M N s t x x') = (term135 M N s t x x').
Proof. exact (@lem8034622 N (s x') (term137 M N t x x')). Qed.
Lemma lem8034624 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term138 M N t x x' y) = (term113 M N t y x x').
Proof. exact (eq_refl (term138 M N t x x' y)). Qed.
Lemma lem8034625 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term143 M N t x x') = (term137 M N t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034624 M N t y x x')). Qed.
Lemma lem8034626 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034627 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term144 M N t x x') = (term145 M N t x x').
Proof. exact (MK_COMB (@lem8034626 N) (@lem8034625 M N t x x')). Qed.
Lemma lem8034628 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034629 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term136 M N s t x x') = (term146 M N s t x x').
Proof. exact (MK_COMB (@lem8034628 M s x') (@lem8034627 M N t x x')). Qed.
Lemma lem8034630 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034631 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term211 M N s t x x') = (term212 M N s t x x').
Proof. exact (MK_COMB (@lem8034630) (@lem8034629 M N s t x x')). Qed.
Lemma lem8034632 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term138 M N t x x' y) = (term113 M N t y x x').
Proof. exact (eq_refl (term138 M N t x x' y)). Qed.
Lemma lem8034633 {M : Type'} (s : type30 M) (x' : cart real M) : (term112 M s x') = (term112 M s x').
Proof. exact (eq_refl (term112 M s x')). Qed.
Lemma lem8034634 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term139 M N s t x x' y) = (term114 M N s t y x x').
Proof. exact (MK_COMB (@lem8034633 M s x') (@lem8034632 M N t y x x')). Qed.
Lemma lem8034635 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term140 M N s t x x') = (term115 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034634 M N s t y x x')). Qed.
Lemma lem8034636 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034637 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term135 M N s t x x') = (term116 M N s t x x').
Proof. exact (MK_COMB (@lem8034636 N) (@lem8034635 M N s t x x')). Qed.
Lemma lem8034638 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : ((term136 M N s t x x') = (term135 M N s t x x')) = ((term146 M N s t x x') = (term116 M N s t x x')).
Proof. exact (MK_COMB (@lem8034631 M N s t x x') (@lem8034637 M N s t x x')). Qed.
Lemma lem8034639 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term146 M N s t x x') = (term116 M N s t x x').
Proof. exact (EQ_MP (@lem8034638 M N s t x x') (@lem8034623 M N s t x x')). Qed.
Lemma lem8034640 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term152 M N s t x x') = (term116 M N s t x x').
Proof. exact (TRANS (@lem8034619 M N s t x x') (@lem8034639 M N s t x x')). Qed.
Lemma lem8034641 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term153 M N s t x) = (term117 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034640 M N s t x x')). Qed.
Lemma lem8034642 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034643 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term154 M N s t x) = (term118 M N s t x).
Proof. exact (MK_COMB (@lem8034642 M) (@lem8034641 M N s t x)). Qed.
Lemma lem8034644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034645 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term206 M N s t x) = (term213 M N s t x).
Proof. exact (MK_COMB (@lem8034644) (@lem8034643 M N s t x)). Qed.
Lemma lem8034646 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8034647 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term207 M N t s x) = (term214 M N t s x).
Proof. exact (MK_COMB (@lem8034645 M N s t x) (@lem8034646 M s x)). Qed.
Lemma lem8034649 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8034650 {M : Type'} (P : type30 M) (Q : Prop) : (term150 M P Q) = (term149 M P Q).
Proof. exact (@lem8034649 (cart real M) P Q). Qed.
Lemma lem8034651 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term215 M N t s x) = (term216 M N t s x).
Proof. exact (@lem8034650 M (term117 M N s t x) (term106 M s x)). Qed.
Lemma lem8034652 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term217 M N s t x x') = (term116 M N s t x x').
Proof. exact (eq_refl (term217 M N s t x x')). Qed.
Lemma lem8034653 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term218 M N s t x) = (term117 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034652 M N s t x x')). Qed.
Lemma lem8034654 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034655 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term219 M N s t x) = (term118 M N s t x).
Proof. exact (MK_COMB (@lem8034654 M) (@lem8034653 M N s t x)). Qed.
Lemma lem8034656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034657 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term220 M N s t x) = (term213 M N s t x).
Proof. exact (MK_COMB (@lem8034656) (@lem8034655 M N s t x)). Qed.
Lemma lem8034658 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8034659 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term215 M N t s x) = (term214 M N t s x).
Proof. exact (MK_COMB (@lem8034657 M N s t x) (@lem8034658 M s x)). Qed.
Lemma lem8034660 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034661 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term221 M N t s x) = (term222 M N t s x).
Proof. exact (MK_COMB (@lem8034660) (@lem8034659 M N t s x)). Qed.
Lemma lem8034662 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term217 M N s t x x') = (term116 M N s t x x').
Proof. exact (eq_refl (term217 M N s t x x')). Qed.
Lemma lem8034663 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034664 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term223 M N s t x x') = (term224 M N s t x x').
Proof. exact (MK_COMB (@lem8034663) (@lem8034662 M N s t x x')). Qed.
Lemma lem8034665 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8034666 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term225 M N t x' s x) = (term226 M N t x' s x).
Proof. exact (MK_COMB (@lem8034664 M N s t x x') (@lem8034665 M s x)). Qed.
Lemma lem8034667 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term227 M N t s x) = (term228 M N t s x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034666 M N t x' s x)). Qed.
Lemma lem8034668 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034669 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term216 M N t s x) = (term229 M N t s x).
Proof. exact (MK_COMB (@lem8034668 M) (@lem8034667 M N t s x)). Qed.
Lemma lem8034670 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : ((term215 M N t s x) = (term216 M N t s x)) = ((term214 M N t s x) = (term229 M N t s x)).
Proof. exact (MK_COMB (@lem8034661 M N t s x) (@lem8034669 M N t s x)). Qed.
Lemma lem8034671 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term214 M N t s x) = (term229 M N t s x).
Proof. exact (EQ_MP (@lem8034670 M N t s x) (@lem8034651 M N t s x)). Qed.
Lemma lem8034673 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term147 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem8034674 {N : Type'} (P : type30 N) (Q : Prop) : (term150 N P Q) = (term149 N P Q).
Proof. exact (@lem8034673 (cart real N) P Q). Qed.
Lemma lem8034675 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term230 M N t x' s x) = (term231 M N t x' s x).
Proof. exact (@lem8034674 N (term115 M N s t x x') (term106 M s x)). Qed.
Lemma lem8034676 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term232 M N s t x x' y) = (term114 M N s t y x x').
Proof. exact (eq_refl (term232 M N s t x x' y)). Qed.
Lemma lem8034677 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term233 M N s t x x') = (term115 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034676 M N s t y x x')). Qed.
Lemma lem8034678 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034679 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term234 M N s t x x') = (term116 M N s t x x').
Proof. exact (MK_COMB (@lem8034678 N) (@lem8034677 M N s t x x')). Qed.
Lemma lem8034680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034681 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term235 M N s t x x') = (term224 M N s t x x').
Proof. exact (MK_COMB (@lem8034680) (@lem8034679 M N s t x x')). Qed.
Lemma lem8034682 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8034683 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term230 M N t x' s x) = (term226 M N t x' s x).
Proof. exact (MK_COMB (@lem8034681 M N s t x x') (@lem8034682 M s x)). Qed.
Lemma lem8034684 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034685 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term236 M N t x' s x) = (term237 M N t x' s x).
Proof. exact (MK_COMB (@lem8034684) (@lem8034683 M N t x' s x)). Qed.
Lemma lem8034686 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term232 M N s t x x' y) = (term114 M N s t y x x').
Proof. exact (eq_refl (term232 M N s t x x' y)). Qed.
Lemma lem8034687 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034688 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term238 M N s t x x' y) = (term239 M N s t y x x').
Proof. exact (MK_COMB (@lem8034687) (@lem8034686 M N s t y x x')). Qed.
Lemma lem8034689 {M : Type'} (s : type30 M) (x : cart real M) : (term106 M s x) = (term106 M s x).
Proof. exact (eq_refl (term106 M s x)). Qed.
Lemma lem8034690 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term240 M N t x' y s x) = (term241 M N t y x' s x).
Proof. exact (MK_COMB (@lem8034688 M N s t y x x') (@lem8034689 M s x)). Qed.
Lemma lem8034691 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term242 M N t x' s x) = (term243 M N t x' s x).
Proof. exact (fun_ext (fun y : cart real N => @lem8034690 M N t y x' s x)). Qed.
Lemma lem8034692 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034693 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term231 M N t x' s x) = (term244 M N t x' s x).
Proof. exact (MK_COMB (@lem8034692 N) (@lem8034691 M N t x' s x)). Qed.
Lemma lem8034694 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : ((term230 M N t x' s x) = (term231 M N t x' s x)) = ((term226 M N t x' s x) = (term244 M N t x' s x)).
Proof. exact (MK_COMB (@lem8034685 M N t x' s x) (@lem8034693 M N t x' s x)). Qed.
Lemma lem8034695 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term226 M N t x' s x) = (term244 M N t x' s x).
Proof. exact (EQ_MP (@lem8034694 M N t x' s x) (@lem8034675 M N t x' s x)). Qed.
Lemma lem8034696 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term228 M N t s x) = (term245 M N t s x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034695 M N t x' s x)). Qed.
Lemma lem8034697 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034698 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term229 M N t s x) = (term246 M N t s x).
Proof. exact (MK_COMB (@lem8034697 M) (@lem8034696 M N t s x)). Qed.
Lemma lem8034699 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term214 M N t s x) = (term246 M N t s x).
Proof. exact (TRANS (@lem8034671 M N t s x) (@lem8034698 M N t s x)). Qed.
Lemma lem8034700 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term207 M N t s x) = (term246 M N t s x).
Proof. exact (TRANS (@lem8034647 M N t s x) (@lem8034699 M N t s x)). Qed.
Lemma lem8034701 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034702 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term208 M N t s x) = (term247 M N t s x).
Proof. exact (MK_COMB (@lem8034701) (@lem8034700 M N t s x)). Qed.
Lemma lem8034703 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term205 M N t s x) = (term205 M N t s x).
Proof. exact (eq_refl (term205 M N t s x)). Qed.
Lemma lem8034704 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term210 M N t s x) = (term248 M N t s x).
Proof. exact (MK_COMB (@lem8034702 M N t s x) (@lem8034703 M N t s x)). Qed.
Lemma lem8034706 {A : Type'} (P : A -> Prop) (Q : Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8034707 {M : Type'} (P : type30 M) (Q : Prop) : (term251 M P Q) = (term252 M P Q).
Proof. exact (@lem8034706 (cart real M) P Q). Qed.
Lemma lem8034708 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term253 M N t s x) = (term254 M N t s x).
Proof. exact (@lem8034707 M (term245 M N t s x) (term205 M N t s x)). Qed.
Lemma lem8034709 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term255 M N t s x x') = (term244 M N t x' s x).
Proof. exact (eq_refl (term255 M N t s x x')). Qed.
Lemma lem8034710 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term256 M N t s x) = (term245 M N t s x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034709 M N t x' s x)). Qed.
Lemma lem8034711 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034712 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term257 M N t s x) = (term246 M N t s x).
Proof. exact (MK_COMB (@lem8034711 M) (@lem8034710 M N t s x)). Qed.
Lemma lem8034713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034714 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term258 M N t s x) = (term247 M N t s x).
Proof. exact (MK_COMB (@lem8034713) (@lem8034712 M N t s x)). Qed.
Lemma lem8034715 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term205 M N t s x) = (term205 M N t s x).
Proof. exact (eq_refl (term205 M N t s x)). Qed.
Lemma lem8034716 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term253 M N t s x) = (term248 M N t s x).
Proof. exact (MK_COMB (@lem8034714 M N t s x) (@lem8034715 M N t s x)). Qed.
Lemma lem8034717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034718 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term259 M N t s x) = (term260 M N t s x).
Proof. exact (MK_COMB (@lem8034717) (@lem8034716 M N t s x)). Qed.
Lemma lem8034719 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term255 M N t s x x') = (term244 M N t x' s x).
Proof. exact (eq_refl (term255 M N t s x x')). Qed.
Lemma lem8034720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034721 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term261 M N t s x x') = (term262 M N t x' s x).
Proof. exact (MK_COMB (@lem8034720) (@lem8034719 M N t x' s x)). Qed.
Lemma lem8034722 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term205 M N t s x) = (term205 M N t s x).
Proof. exact (eq_refl (term205 M N t s x)). Qed.
Lemma lem8034723 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term263 M N x' t s x) = (term264 M N x' t s x).
Proof. exact (MK_COMB (@lem8034721 M N t x' s x) (@lem8034722 M N t s x)). Qed.
Lemma lem8034724 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term265 M N t s x) = (term266 M N t s x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034723 M N x' t s x)). Qed.
Lemma lem8034725 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034726 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term254 M N t s x) = (term267 M N t s x).
Proof. exact (MK_COMB (@lem8034725 M) (@lem8034724 M N t s x)). Qed.
Lemma lem8034727 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : ((term253 M N t s x) = (term254 M N t s x)) = ((term248 M N t s x) = (term267 M N t s x)).
Proof. exact (MK_COMB (@lem8034718 M N t s x) (@lem8034726 M N t s x)). Qed.
Lemma lem8034728 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term248 M N t s x) = (term267 M N t s x).
Proof. exact (EQ_MP (@lem8034727 M N t s x) (@lem8034708 M N t s x)). Qed.
Lemma lem8034730 {A : Type'} (P : A -> Prop) (Q : Prop) : (term249 A P Q) = (term250 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem8034731 {N : Type'} (P : type30 N) (Q : Prop) : (term251 N P Q) = (term252 N P Q).
Proof. exact (@lem8034730 (cart real N) P Q). Qed.
Lemma lem8034732 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term268 M N x' t s x) = (term269 M N x' t s x).
Proof. exact (@lem8034731 N (term243 M N t x' s x) (term205 M N t s x)). Qed.
Lemma lem8034733 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term270 M N t x' s x y) = (term241 M N t y x' s x).
Proof. exact (eq_refl (term270 M N t x' s x y)). Qed.
Lemma lem8034734 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term271 M N t x' s x) = (term243 M N t x' s x).
Proof. exact (fun_ext (fun y : cart real N => @lem8034733 M N t y x' s x)). Qed.
Lemma lem8034735 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034736 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term272 M N t x' s x) = (term244 M N t x' s x).
Proof. exact (MK_COMB (@lem8034735 N) (@lem8034734 M N t x' s x)). Qed.
Lemma lem8034737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034738 {M N : Type'} (t : type30 N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term273 M N t x' s x) = (term262 M N t x' s x).
Proof. exact (MK_COMB (@lem8034737) (@lem8034736 M N t x' s x)). Qed.
Lemma lem8034739 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term205 M N t s x) = (term205 M N t s x).
Proof. exact (eq_refl (term205 M N t s x)). Qed.
Lemma lem8034740 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term268 M N x' t s x) = (term264 M N x' t s x).
Proof. exact (MK_COMB (@lem8034738 M N t x' s x) (@lem8034739 M N t s x)). Qed.
Lemma lem8034741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034742 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term274 M N x' t s x) = (term275 M N x' t s x).
Proof. exact (MK_COMB (@lem8034741) (@lem8034740 M N x' t s x)). Qed.
Lemma lem8034743 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term270 M N t x' s x y) = (term241 M N t y x' s x).
Proof. exact (eq_refl (term270 M N t x' s x y)). Qed.
Lemma lem8034744 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034745 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term276 M N t x' s x y) = (term277 M N t y x' s x).
Proof. exact (MK_COMB (@lem8034744) (@lem8034743 M N t y x' s x)). Qed.
Lemma lem8034746 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term205 M N t s x) = (term205 M N t s x).
Proof. exact (eq_refl (term205 M N t s x)). Qed.
Lemma lem8034747 {M N : Type'} (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term278 M N x' y t s x) = (term279 M N y x' t s x).
Proof. exact (MK_COMB (@lem8034745 M N t y x' s x) (@lem8034746 M N t s x)). Qed.
Lemma lem8034748 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term280 M N x' t s x) = (term281 M N x' t s x).
Proof. exact (fun_ext (fun y : cart real N => @lem8034747 M N y x' t s x)). Qed.
Lemma lem8034749 {N : Type'} : (@ex (cart real N)) = (@ex (cart real N)).
Proof. exact (eq_refl (@ex (cart real N))). Qed.
Lemma lem8034750 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term269 M N x' t s x) = (term282 M N x' t s x).
Proof. exact (MK_COMB (@lem8034749 N) (@lem8034748 M N x' t s x)). Qed.
Lemma lem8034751 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : ((term268 M N x' t s x) = (term269 M N x' t s x)) = ((term264 M N x' t s x) = (term282 M N x' t s x)).
Proof. exact (MK_COMB (@lem8034742 M N x' t s x) (@lem8034750 M N x' t s x)). Qed.
Lemma lem8034752 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term264 M N x' t s x) = (term282 M N x' t s x).
Proof. exact (EQ_MP (@lem8034751 M N x' t s x) (@lem8034732 M N x' t s x)). Qed.
Lemma lem8034753 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term266 M N t s x) = (term283 M N t s x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034752 M N x' t s x)). Qed.
Lemma lem8034754 {M : Type'} : (@ex (cart real M)) = (@ex (cart real M)).
Proof. exact (eq_refl (@ex (cart real M))). Qed.
Lemma lem8034755 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term267 M N t s x) = (term284 M N t s x).
Proof. exact (MK_COMB (@lem8034754 M) (@lem8034753 M N t s x)). Qed.
Lemma lem8034756 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term248 M N t s x) = (term284 M N t s x).
Proof. exact (TRANS (@lem8034728 M N t s x) (@lem8034755 M N t s x)). Qed.
Lemma lem8034758 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term210 M N t s x) = (term284 M N t s x).
Proof. exact (TRANS (@lem8034704 M N t s x) (@lem8034756 M N t s x)). Qed.
Lemma lem8034759 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term171 M N t s x) = (term284 M N t s x).
Proof. exact (TRANS (@lem8034528 M N t s x) (@lem8034758 M N t s x)). Qed.
Lemma lem8034760 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term171 M N t s x) : term284 M N t s x.
Proof. exact (EQ_MP (@lem8034759 M N t s x) (@lem8034445 M N t s x h1)). Qed.
Lemma lem8034761 {M N : Type'} (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term282 M N x' t s x) : term282 M N x' t s x.
Proof. exact (h1). Qed.
Lemma lem8034762 {M N : Type'} (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term279 M N y x' t s x) : term279 M N y x' t s x.
Proof. exact (h1). Qed.
Lemma lem8034766 {M : Type'} (s : type30 M) (x : cart real M) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem8034773 {M : Type'} (x : cart real M) (x' : cart real M) : (term185 M x x') = (term185 M x x').
Proof. exact (eq_refl (term185 M x x')). Qed.
Lemma lem8034778 {N : Type'} (t : type30 N) (y : cart real N) : (term106 N t y) = (term106 N t y).
Proof. exact (eq_refl (term106 N t y)). Qed.
Lemma lem8034779 {N : Type'} (t : type30 N) : (term108 N t) = (term108 N t).
Proof. exact (fun_ext (fun y : cart real N => @lem8034778 N t y)). Qed.
Lemma lem8034780 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034781 {N : Type'} (t : type30 N) : (term109 N t) = (term109 N t).
Proof. exact (MK_COMB (@lem8034780 N) (@lem8034779 N t)). Qed.
Lemma lem8034782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034783 {N : Type'} (t : type30 N) : (term187 N t) = (term187 N t).
Proof. exact (MK_COMB (@lem8034782) (@lem8034781 N t)). Qed.
Lemma lem8034784 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term189 M N t x x') = (term189 M N t x x').
Proof. exact (MK_COMB (@lem8034783 N t) (@lem8034773 M x x')). Qed.
Lemma lem8034791 {M : Type'} (s : type30 M) (x' : cart real M) : (term191 M s x') = (term191 M s x').
Proof. exact (eq_refl (term191 M s x')). Qed.
Lemma lem8034792 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term193 M N s t x x') = (term193 M N s t x x').
Proof. exact (MK_COMB (@lem8034791 M s x') (@lem8034784 M N t x x')). Qed.
Lemma lem8034793 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term200 M N s t x) = (term200 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034792 M N s t x x')). Qed.
Lemma lem8034794 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034795 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term201 M N s t x) = (term201 M N s t x).
Proof. exact (MK_COMB (@lem8034794 M) (@lem8034793 M N s t x)). Qed.
Lemma lem8034796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8034797 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term203 M N s t x) = (term203 M N s t x).
Proof. exact (MK_COMB (@lem8034796) (@lem8034795 M N s t x)). Qed.
Lemma lem8034798 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) : (term205 M N t s x) = (term205 M N t s x).
Proof. exact (MK_COMB (@lem8034797 M N s t x) (@lem8034766 M s x)). Qed.
Lemma lem8034825 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) : (term277 M N t y x' s x) = (term277 M N t y x' s x).
Proof. exact (eq_refl (term277 M N t y x' s x)). Qed.
Lemma lem8034826 {M N : Type'} (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) : (term279 M N y x' t s x) = (term279 M N y x' t s x).
Proof. exact (MK_COMB (@lem8034825 M N t y x' s x) (@lem8034798 M N t s x)). Qed.
Lemma lem8034827 {M N : Type'} (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term279 M N y x' t s x) : term279 M N y x' t s x.
Proof. exact (EQ_MP (@lem8034826 M N y x' t s x) (@lem8034762 M N y x' t s x h1)). Qed.
Lemma lem8034831 {N : Type'} (t : type30 N) (x'' : cart real N) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem8034832 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term241 M N t y x' s x.
Proof. exact (h1). Qed.
Lemma lem8034833 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term205 M N t s x.
Proof. exact (h1). Qed.
Lemma lem8034835 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term114 M N s t y x x'.
Proof. exact (proj1 (@lem8034832 M N t y x' s x h1)). Qed.
Lemma lem8034836 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term113 M N t y x x'.
Proof. exact (proj2 (@lem8034835 M N t y x' s x h1)). Qed.
Lemma lem8034841 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term201 M N s t x.
Proof. exact (proj1 (@lem8034833 M N t s x h1)). Qed.
Lemma lem8034865 {N : Type'} (t : type30 N) (x'' : cart real N) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem8034867 {A : Type'} (P : A -> Prop) (Q : Prop) : (term285 A P Q) = (term286 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem8034868 {N : Type'} (P : type30 N) (Q : Prop) : (term287 N P Q) = (term288 N P Q).
Proof. exact (@lem8034867 (cart real N) P Q). Qed.
Lemma lem8034869 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term289 M N t x x') = (term290 M N t x x').
Proof. exact (@lem8034868 N (term108 N t) (term185 M x x')). Qed.
Lemma lem8034870 {N : Type'} (t : type30 N) (y : cart real N) : (term176 N t y) = (term106 N t y).
Proof. exact (eq_refl (term176 N t y)). Qed.
Lemma lem8034871 {N : Type'} (t : type30 N) : (term291 N t) = (term108 N t).
Proof. exact (fun_ext (fun y : cart real N => @lem8034870 N t y)). Qed.
Lemma lem8034872 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034873 {N : Type'} (t : type30 N) : (term292 N t) = (term109 N t).
Proof. exact (MK_COMB (@lem8034872 N) (@lem8034871 N t)). Qed.
Lemma lem8034874 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034875 {N : Type'} (t : type30 N) : (term293 N t) = (term187 N t).
Proof. exact (MK_COMB (@lem8034874) (@lem8034873 N t)). Qed.
Lemma lem8034876 {M : Type'} (x : cart real M) (x' : cart real M) : (term185 M x x') = (term185 M x x').
Proof. exact (eq_refl (term185 M x x')). Qed.
Lemma lem8034877 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term289 M N t x x') = (term189 M N t x x').
Proof. exact (MK_COMB (@lem8034875 N t) (@lem8034876 M x x')). Qed.
Lemma lem8034878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034879 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term294 M N t x x') = (term295 M N t x x').
Proof. exact (MK_COMB (@lem8034878) (@lem8034877 M N t x x')). Qed.
Lemma lem8034880 {N : Type'} (t : type30 N) (y : cart real N) : (term176 N t y) = (term106 N t y).
Proof. exact (eq_refl (term176 N t y)). Qed.
Lemma lem8034881 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem8034882 {N : Type'} (t : type30 N) (y : cart real N) : (term296 N t y) = (term191 N t y).
Proof. exact (MK_COMB (@lem8034881) (@lem8034880 N t y)). Qed.
Lemma lem8034883 {M : Type'} (x : cart real M) (x' : cart real M) : (term185 M x x') = (term185 M x x').
Proof. exact (eq_refl (term185 M x x')). Qed.
Lemma lem8034884 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term297 M N t y x x') = (term298 M N t y x x').
Proof. exact (MK_COMB (@lem8034882 N t y) (@lem8034883 M x x')). Qed.
Lemma lem8034885 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term299 M N t x x') = (term300 M N t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034884 M N t y x x')). Qed.
Lemma lem8034886 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034887 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term290 M N t x x') = (term301 M N t x x').
Proof. exact (MK_COMB (@lem8034886 N) (@lem8034885 M N t x x')). Qed.
Lemma lem8034888 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : ((term289 M N t x x') = (term290 M N t x x')) = ((term189 M N t x x') = (term301 M N t x x')).
Proof. exact (MK_COMB (@lem8034879 M N t x x') (@lem8034887 M N t x x')). Qed.
Lemma lem8034889 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term189 M N t x x') = (term301 M N t x x').
Proof. exact (EQ_MP (@lem8034888 M N t x x') (@lem8034869 M N t x x')). Qed.
Lemma lem8034890 {M : Type'} (s : type30 M) (x' : cart real M) : (term191 M s x') = (term191 M s x').
Proof. exact (eq_refl (term191 M s x')). Qed.
Lemma lem8034891 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term193 M N s t x x') = (term302 M N s t x x').
Proof. exact (MK_COMB (@lem8034890 M s x') (@lem8034889 M N t x x')). Qed.
Lemma lem8034893 {A : Type'} (P : Prop) (Q : A -> Prop) : (term303 A P Q) = (term304 A P Q).
Proof. exact (EQ_MP (@lem19007 A P Q) (@lem19006 A P Q)). Qed.
Lemma lem8034894 {N : Type'} (P : Prop) (Q : type30 N) : (term305 N P Q) = (term306 N P Q).
Proof. exact (@lem8034893 (cart real N) P Q). Qed.
Lemma lem8034895 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term307 M N s t x x') = (term308 M N s t x x').
Proof. exact (@lem8034894 N (term106 M s x') (term300 M N t x x')). Qed.
Lemma lem8034896 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term309 M N t x x' y) = (term298 M N t y x x').
Proof. exact (eq_refl (term309 M N t x x' y)). Qed.
Lemma lem8034897 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term310 M N t x x') = (term300 M N t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034896 M N t y x x')). Qed.
Lemma lem8034898 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034899 {M N : Type'} (t : type30 N) (x : cart real M) (x' : cart real M) : (term311 M N t x x') = (term301 M N t x x').
Proof. exact (MK_COMB (@lem8034898 N) (@lem8034897 M N t x x')). Qed.
Lemma lem8034900 {M : Type'} (s : type30 M) (x' : cart real M) : (term191 M s x') = (term191 M s x').
Proof. exact (eq_refl (term191 M s x')). Qed.
Lemma lem8034901 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term307 M N s t x x') = (term302 M N s t x x').
Proof. exact (MK_COMB (@lem8034900 M s x') (@lem8034899 M N t x x')). Qed.
Lemma lem8034902 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8034903 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term312 M N s t x x') = (term313 M N s t x x').
Proof. exact (MK_COMB (@lem8034902) (@lem8034901 M N s t x x')). Qed.
Lemma lem8034904 {M N : Type'} (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term309 M N t x x' y) = (term298 M N t y x x').
Proof. exact (eq_refl (term309 M N t x x' y)). Qed.
Lemma lem8034905 {M : Type'} (s : type30 M) (x' : cart real M) : (term191 M s x') = (term191 M s x').
Proof. exact (eq_refl (term191 M s x')). Qed.
Lemma lem8034906 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term314 M N s t x x' y) = (term315 M N s t y x x').
Proof. exact (MK_COMB (@lem8034905 M s x') (@lem8034904 M N t y x x')). Qed.
Lemma lem8034907 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term316 M N s t x x') = (term317 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034906 M N s t y x x')). Qed.
Lemma lem8034908 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034909 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term308 M N s t x x') = (term318 M N s t x x').
Proof. exact (MK_COMB (@lem8034908 N) (@lem8034907 M N s t x x')). Qed.
Lemma lem8034910 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : ((term307 M N s t x x') = (term308 M N s t x x')) = ((term302 M N s t x x') = (term318 M N s t x x')).
Proof. exact (MK_COMB (@lem8034903 M N s t x x') (@lem8034909 M N s t x x')). Qed.
Lemma lem8034911 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term302 M N s t x x') = (term318 M N s t x x').
Proof. exact (EQ_MP (@lem8034910 M N s t x x') (@lem8034895 M N s t x x')). Qed.
Lemma lem8034912 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term193 M N s t x x') = (term318 M N s t x x').
Proof. exact (TRANS (@lem8034891 M N s t x x') (@lem8034911 M N s t x x')). Qed.
Lemma lem8034913 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term200 M N s t x) = (term319 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034912 M N s t x x')). Qed.
Lemma lem8034914 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034915 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term201 M N s t x) = (term320 M N s t x).
Proof. exact (MK_COMB (@lem8034914 M) (@lem8034913 M N s t x)). Qed.
Lemma lem8034928 {M N : Type'} (s : type30 M) (t : type30 N) (y : cart real N) (x : cart real M) (x' : cart real M) : (term315 M N s t y x x') = (term315 M N s t y x x').
Proof. exact (eq_refl (term315 M N s t y x x')). Qed.
Lemma lem8034929 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term317 M N s t x x') = (term317 M N s t x x').
Proof. exact (fun_ext (fun y : cart real N => @lem8034928 M N s t y x x')). Qed.
Lemma lem8034930 {N : Type'} : (@all (cart real N)) = (@all (cart real N)).
Proof. exact (eq_refl (@all (cart real N))). Qed.
Lemma lem8034931 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (x' : cart real M) : (term318 M N s t x x') = (term318 M N s t x x').
Proof. exact (MK_COMB (@lem8034930 N) (@lem8034929 M N s t x x')). Qed.
Lemma lem8034932 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term319 M N s t x) = (term319 M N s t x).
Proof. exact (fun_ext (fun x' : cart real M => @lem8034931 M N s t x x')). Qed.
Lemma lem8034933 {M : Type'} : (@all (cart real M)) = (@all (cart real M)).
Proof. exact (eq_refl (@all (cart real M))). Qed.
Lemma lem8034934 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term320 M N s t x) = (term320 M N s t x).
Proof. exact (MK_COMB (@lem8034933 M) (@lem8034932 M N s t x)). Qed.
Lemma lem8034935 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) : (term201 M N s t x) = (term320 M N s t x).
Proof. exact (TRANS (@lem8034915 M N s t x) (@lem8034934 M N s t x)). Qed.
Lemma lem8034936 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term320 M N s t x.
Proof. exact (EQ_MP (@lem8034935 M N s t x) (@lem8034841 M N t s x h1)). Qed.
Lemma lem8034941 {M N : Type'} (_106075 : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term321 M N s t x _106075.
Proof. exact (@lem8034936 M N t s x h1 _106075). Qed.
Lemma lem8034942 {M N : Type'} (s : type30 M) (t : type30 N) (x : cart real M) (_106075 : cart real M) : (term321 M N s t x _106075) = (term318 M N s t x _106075).
Proof. exact (eq_refl (term321 M N s t x _106075)). Qed.
Lemma lem8034943 {M N : Type'} (_106075 : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term318 M N s t x _106075.
Proof. exact (EQ_MP (@lem8034942 M N s t x _106075) (@lem8034941 M N _106075 t s x h1)). Qed.
Lemma lem8034944 {M N : Type'} (_106075 : cart real M) (_106076 : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term322 M N s t x _106075 _106076.
Proof. exact (@lem8034943 M N _106075 t s x h1 _106076). Qed.
Lemma lem8034945 {M N : Type'} (s : type30 M) (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term322 M N s t x _106075 _106076) = (term315 M N s t _106076 x _106075).
Proof. exact (eq_refl (term322 M N s t x _106075 _106076)). Qed.
Lemma lem8034950 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term106 M s x.
Proof. exact (proj2 (@lem8034832 M N t y x' s x h1)). Qed.
Lemma lem8034956 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : x = x'.
Proof. exact (proj2 (@lem8034836 M N t y x' s x h1)). Qed.
Lemma lem8034958 {N : Type'} (t : type30 N) (x'' : cart real N) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem8034968 {M N : Type'} (_106076 : cart real N) (_106075 : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term315 M N s t _106076 x _106075.
Proof. exact (EQ_MP (@lem8034945 M N s t _106076 x _106075) (@lem8034944 M N _106075 _106076 t s x h1)). Qed.
Lemma lem8034999 {M : Type'} (s : type30 M) : (term108 M s) = (term108 M s).
Proof. exact (eq_refl (term108 M s)). Qed.
Lemma lem8035000 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : (term176 M s x) = (term176 M s x').
Proof. exact (MK_COMB (@lem8034999 M s) (@lem8034956 M N t y x' s x h1)). Qed.
Lemma lem8035001 {M : Type'} (s : type30 M) (x' : cart real M) : (term176 M s x') = (term106 M s x').
Proof. exact (eq_refl (term176 M s x')). Qed.
Lemma lem8035002 {M : Type'} (s : type30 M) (x : cart real M) : (term323 M s x) = (term323 M s x).
Proof. exact (eq_refl (term323 M s x)). Qed.
Lemma lem8035003 {M : Type'} (x : cart real M) (s : type30 M) (x' : cart real M) : ((term176 M s x) = (term176 M s x')) = ((term176 M s x) = (term106 M s x')).
Proof. exact (MK_COMB (@lem8035002 M s x) (@lem8035001 M s x')). Qed.
Lemma lem8035004 {M : Type'} (s : type30 M) (x : cart real M) : (term176 M s x) = (term106 M s x).
Proof. exact (eq_refl (term176 M s x)). Qed.
Lemma lem8035005 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8035006 {M : Type'} (s : type30 M) (x : cart real M) : (term323 M s x) = (term324 M s x).
Proof. exact (MK_COMB (@lem8035005) (@lem8035004 M s x)). Qed.
Lemma lem8035007 {M : Type'} (s : type30 M) (x' : cart real M) : (term106 M s x') = (term106 M s x').
Proof. exact (eq_refl (term106 M s x')). Qed.
Lemma lem8035008 {M : Type'} (x : cart real M) (s : type30 M) (x' : cart real M) : ((term176 M s x) = (term106 M s x')) = ((term106 M s x) = (term106 M s x')).
Proof. exact (MK_COMB (@lem8035006 M s x) (@lem8035007 M s x')). Qed.
Lemma lem8035009 {M : Type'} (x : cart real M) (s : type30 M) (x' : cart real M) : ((term176 M s x) = (term176 M s x')) = ((term106 M s x) = (term106 M s x')).
Proof. exact (TRANS (@lem8035003 M x s x') (@lem8035008 M x s x')). Qed.
Lemma lem8035010 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : (term106 M s x) = (term106 M s x').
Proof. exact (EQ_MP (@lem8035009 M x s x') (@lem8035000 M N t y x' s x h1)). Qed.
Lemma lem8035011 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term106 M s x'.
Proof. exact (EQ_MP (@lem8035010 M N t y x' s x h1) (@lem8034950 M N t y x' s x h1)). Qed.
Lemma lem8035041 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : s x'.
Proof. exact (proj1 (@lem8034835 M N t y x' s x h1)). Qed.
Lemma lem8035042 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term325 M s x'.
Proof. exact (fun h0 : term106 M s x' => @lem8035041 M N t y x' s x h1). Qed.
Lemma lem8035044 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8035045 {M : Type'} (s : type30 M) (x' : cart real M) : (term325 M s x') = (s x').
Proof. exact (@lem8035044 (s x')). Qed.
Lemma lem8035046 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : s x'.
Proof. exact (EQ_MP (@lem8035045 M s x') (@lem8035042 M N t y x' s x h1)). Qed.
Lemma lem8035049 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8035051 {M : Type'} (s : type30 M) (x' : cart real M) : (term106 M s x') = (term327 M s x').
Proof. exact (@lem8035049 (s x')). Qed.
Lemma lem8035054 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term327 M s x'.
Proof. exact (EQ_MP (@lem8035051 M s x') (@lem8035011 M N t y x' s x h1)). Qed.
Lemma lem8035057 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : False.
Proof. exact (@lem8035054 M N t y x' s x h1 (@lem8035046 M N t y x' s x h1)). Qed.
Lemma lem8035058 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : term328.
Proof. exact (fun h0 : ~ False => @lem8035057 M N t y x' s x h1). Qed.
Lemma lem8035060 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8035061 : term328 = False.
Proof. exact (@lem8035060 False). Qed.
Lemma lem8035092 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : s x.
Proof. exact (proj2 (@lem8034833 M N t s x h1)). Qed.
Lemma lem8035093 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term325 M s x.
Proof. exact (fun h0 : term106 M s x => @lem8035092 M N t s x h1). Qed.
Lemma lem8035095 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8035096 {M : Type'} (s : type30 M) (x : cart real M) : (term325 M s x) = (s x).
Proof. exact (@lem8035095 (s x)). Qed.
Lemma lem8035097 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : s x.
Proof. exact (EQ_MP (@lem8035096 M s x) (@lem8035093 M N t s x h1)). Qed.
Lemma lem8035099 {N : Type'} (t : type30 N) (x'' : cart real N) (h1 : t x'') : t x''.
Proof. exact (h1). Qed.
Lemma lem8035100 {N : Type'} (t : type30 N) (x'' : cart real N) (h1 : t x'') : term325 N t x''.
Proof. exact (fun h0 : term106 N t x'' => @lem8035099 N t x'' h1). Qed.
Lemma lem8035102 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8035103 {N : Type'} (t : type30 N) (x'' : cart real N) : (term325 N t x'') = (t x'').
Proof. exact (@lem8035102 (t x'')). Qed.
Lemma lem8035104 {N : Type'} (t : type30 N) (x'' : cart real N) (h1 : t x'') : t x''.
Proof. exact (EQ_MP (@lem8035103 N t x'') (@lem8035100 N t x'' h1)). Qed.
Lemma lem8035106 {M : Type'} (x : cart real M) : x = x.
Proof. exact (@lem21386 (cart real M) x). Qed.
Lemma lem8035107 {M : Type'} (x : cart real M) : x = x.
Proof. exact (@lem8035106 M x). Qed.
Lemma lem8035108 {M : Type'} (x : cart real M) : term329 M x.
Proof. exact (fun h0 : term330 M x => @lem8035107 M x). Qed.
Lemma lem8035110 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8035111 {M : Type'} (x : cart real M) : (term329 M x) = (x = x).
Proof. exact (@lem8035110 (x = x)). Qed.
Lemma lem8035112 {M : Type'} (x : cart real M) : x = x.
Proof. exact (EQ_MP (@lem8035111 M x) (@lem8035108 M x)). Qed.
Lemma lem8035114 (a : Prop) (b : Prop) : (term331 a b) = (term332 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8035115 {M N : Type'} (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term298 M N t _106076 x _106075) = (term333 M N t _106076 x _106075).
Proof. exact (@lem8035114 (t _106076) (x = _106075)). Qed.
Lemma lem8035116 {M : Type'} (s : type30 M) (_106075 : cart real M) : (term191 M s _106075) = (term191 M s _106075).
Proof. exact (eq_refl (term191 M s _106075)). Qed.
Lemma lem8035117 {M N : Type'} (s : type30 M) (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term315 M N s t _106076 x _106075) = (term334 M N s t _106076 x _106075).
Proof. exact (MK_COMB (@lem8035116 M s _106075) (@lem8035115 M N t _106076 x _106075)). Qed.
Lemma lem8035119 (a : Prop) (b : Prop) : (term331 a b) = (term332 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem8035120 {M N : Type'} (s : type30 M) (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term334 M N s t _106076 x _106075) = (term335 M N s t _106076 x _106075).
Proof. exact (@lem8035119 (s _106075) (term113 M N t _106076 x _106075)). Qed.
Lemma lem8035121 {M N : Type'} (s : type30 M) (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term315 M N s t _106076 x _106075) = (term335 M N s t _106076 x _106075).
Proof. exact (TRANS (@lem8035117 M N s t _106076 x _106075) (@lem8035120 M N s t _106076 x _106075)). Qed.
Lemma lem8035123 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem8035124 {M N : Type'} (s : type30 M) (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term335 M N s t _106076 x _106075) = (term336 M N s t _106076 x _106075).
Proof. exact (@lem8035123 (term114 M N s t _106076 x _106075)). Qed.
Lemma lem8035125 {M N : Type'} (s : type30 M) (t : type30 N) (_106076 : cart real N) (x : cart real M) (_106075 : cart real M) : (term315 M N s t _106076 x _106075) = (term336 M N s t _106076 x _106075).
Proof. exact (TRANS (@lem8035121 M N s t _106076 x _106075) (@lem8035124 M N s t _106076 x _106075)). Qed.
Lemma lem8035127 {M N : Type'} (x : cart real M) (t : type30 N) (x'' : cart real N) (h1 : t x'') : term337 M N t x'' x.
Proof. exact (conj (@lem8035104 N t x'' h1) (@lem8035112 M x)). Qed.
Lemma lem8035128 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : term338 M N s t x'' x.
Proof. exact (conj (@lem8035097 M N t s x h2) (@lem8035127 M N x t x'' h1)). Qed.
Lemma lem8035130 {M N : Type'} (_106076 : cart real N) (_106075 : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term336 M N s t _106076 x _106075.
Proof. exact (EQ_MP (@lem8035125 M N s t _106076 x _106075) (@lem8034968 M N _106076 _106075 t s x h1)). Qed.
Lemma lem8035131 {M N : Type'} (_106076 : cart real N) (_106075 : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term336 M N s t _106076 x _106075.
Proof. exact (@lem8035130 M N _106076 _106075 t s x h1). Qed.
Lemma lem8035132 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term205 M N t s x) : term339 M N s t x'' x.
Proof. exact (@lem8035131 M N x'' x t s x h1). Qed.
Lemma lem8035135 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : False.
Proof. exact (@lem8035132 M N x'' t s x h2 (@lem8035128 M N x'' t s x h1 h2)). Qed.
Lemma lem8035136 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : term328.
Proof. exact (fun h0 : ~ False => @lem8035135 M N x'' t s x h1 h2). Qed.
Lemma lem8035138 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem8035139 : term328 = False.
Proof. exact (@lem8035138 False). Qed.
Lemma lem8035140 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : False.
Proof. exact (EQ_MP (@lem8035139) (@lem8035136 M N x'' t s x h1 h2)). Qed.
Lemma lem8035141 {M N : Type'} (t : type30 N) (y : cart real N) (x' : cart real M) (s : type30 M) (x : cart real M) (h1 : term241 M N t y x' s x) : False.
Proof. exact (EQ_MP (@lem8035061) (@lem8035058 M N t y x' s x h1)). Qed.
Lemma lem8035142 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem8035140 M N x'' t s x h1 h2) (fun h3 : False => @lem8034958 N t x'' h1)). Qed.
Lemma lem8035143 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : False.
Proof. exact (EQ_MP (@lem8035142 M N x'' t s x h1 h2) (@lem8034958 N t x'' h1)). Qed.
Lemma lem8035144 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem8035143 M N x'' t s x h1 h2) (fun h3 : False => @lem8034865 N t x'' h1)). Qed.
Lemma lem8035145 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : False.
Proof. exact (EQ_MP (@lem8035144 M N x'' t s x h1 h2) (@lem8034865 N t x'' h1)). Qed.
Lemma lem8035146 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem8035145 M N x'' t s x h1 h2) (fun h3 : False => @lem8034865 N t x'' h1)). Qed.
Lemma lem8035147 {M N : Type'} (x'' : cart real N) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term205 M N t s x) : False.
Proof. exact (EQ_MP (@lem8035146 M N x'' t s x h1 h2) (@lem8034865 N t x'' h1)). Qed.
Lemma lem8035148 {M N : Type'} (x'' : cart real N) (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term279 M N y x' t s x) : False.
Proof. exact (or_elim (@lem8034827 M N y x' t s x h2) (fun h0 : term241 M N t y x' s x => @lem8035141 M N t y x' s x h0) (fun h0 : term205 M N t s x => @lem8035147 M N x'' t s x h1 h0)). Qed.
Lemma lem8035149 {M N : Type'} (x'' : cart real N) (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term279 M N y x' t s x) : (t x'') = False.
Proof. exact (prop_ext (fun h3 : t x'' => @lem8035148 M N x'' y x' t s x h1 h2) (fun h3 : False => @lem8034831 N t x'' h1)). Qed.
Lemma lem8035150 {M N : Type'} (x'' : cart real N) (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term279 M N y x' t s x) : False.
Proof. exact (EQ_MP (@lem8035149 M N x'' y x' t s x h1 h2) (@lem8034831 N t x'' h1)). Qed.
Lemma lem8035151 {M N : Type'} (x'' : cart real N) (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term279 M N y x' t s x) : (term279 M N y x' t s x) = False.
Proof. exact (prop_ext (fun h3 : term279 M N y x' t s x => @lem8035150 M N x'' y x' t s x h1 h2) (fun h3 : False => @lem8034827 M N y x' t s x h2)). Qed.
Lemma lem8035152 {M N : Type'} (x'' : cart real N) (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : t x'') (h2 : term279 M N y x' t s x) : False.
Proof. exact (EQ_MP (@lem8035151 M N x'' y x' t s x h1 h2) (@lem8034827 M N y x' t s x h2)). Qed.
Lemma lem8035153 {M N : Type'} (y : cart real N) (x' : cart real M) (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term110 N t) (h2 : term279 M N y x' t s x) : False.
Proof. exact (ex_elim (@lem8034467 N t h1) (fun x'' : cart real N => fun h0 : term167 N t x'' => @lem8035152 M N x'' y x' t s x h0 h2)). Qed.
Lemma lem8035154 {M N : Type'} (x' : cart real M) (s : type30 M) (x : cart real M) (t : type30 N) (h1 : term282 M N x' t s x) (h2 : term110 N t) : False.
Proof. exact (ex_elim (@lem8034761 M N x' t s x h1) (fun y : cart real N => fun h0 : term281 M N x' t s x y => @lem8035153 M N y x' t s x h2 h0)). Qed.
Lemma lem8035155 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term110 N t) (h2 : term171 M N t s x) : False.
Proof. exact (ex_elim (@lem8034760 M N t s x h2) (fun x' : cart real M => fun h0 : term283 M N t s x x' => @lem8035154 M N x' s x t h0 h1)). Qed.
Lemma lem8035156 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term110 N t) (h2 : term171 M N t s x) : (term171 M N t s x) = False.
Proof. exact (prop_ext (fun h3 : term171 M N t s x => @lem8035155 M N t s x h1 h2) (fun h3 : False => @lem8034445 M N t s x h2)). Qed.
Lemma lem8035157 {M N : Type'} (t : type30 N) (s : type30 M) (x : cart real M) (h1 : term110 N t) (h2 : term171 M N t s x) : False.
Proof. exact (EQ_MP (@lem8035156 M N t s x h1 h2) (@lem8034445 M N t s x h2)). Qed.
Lemma lem8035158 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (h1 : term110 N t) : term170 M N t s x.
Proof. exact (fun h0 : term171 M N t s x => @lem8035157 M N t s x h1 h0). Qed.
Lemma lem8035159 {M N : Type'} (s : type30 M) (x : cart real M) (t : type30 N) (h1 : term110 N t) : (term154 M N s t x) = (s x).
Proof. exact (EQ_MP (@lem8034444 M N t s x) (@lem8035158 M N s x t h1)). Qed.
Lemma lem8035164 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term110 N t) : term157 M N t s.
Proof. exact (fun x : cart real M => @lem8035159 M N s x t h1). Qed.
Lemma lem8035165 {M N : Type'} (t : type30 N) (s : type30 M) : term158 M N t s.
Proof. exact (fun h0 : term110 N t => @lem8035164 M N s t h0). Qed.
Lemma lem8035170 {M N : Type'} (s : type30 M) : term162 M N s.
Proof. exact (fun t : type30 N => @lem8035165 M N t s). Qed.
Lemma lem8035175 {M N : Type'} : term166 M N.
Proof. exact (fun s : type30 M => @lem8035170 M N s). Qed.
Lemma lem8035176 {M N : Type'} : term165 M N.
Proof. exact (EQ_MP (@lem8034439 M N) (@lem8035175 M N)). Qed.
Lemma lem8035177 {M N : Type'} (s : type30 M) : term340 M N s.
Proof. exact (@lem8035176 M N s). Qed.
Lemma lem8035178 {M N : Type'} (s : type30 M) : (term340 M N s) = (term161 M N s).
Proof. exact (eq_refl (term340 M N s)). Qed.
Lemma lem8035179 {M N : Type'} (s : type30 M) : term161 M N s.
Proof. exact (EQ_MP (@lem8035178 M N s) (@lem8035177 M N s)). Qed.
Lemma lem8035180 {M N : Type'} (s : type30 M) (t : type30 N) : term341 M N s t.
Proof. exact (@lem8035179 M N s t). Qed.
Lemma lem8035181 {M N : Type'} (t : type30 N) (s : type30 M) : (term341 M N s t) = (term124 M N t s).
Proof. exact (eq_refl (term341 M N s t)). Qed.
Lemma lem8035182 {M N : Type'} (t : type30 N) (s : type30 M) : term124 M N t s.
Proof. exact (EQ_MP (@lem8035181 M N t s) (@lem8035180 M N s t)). Qed.
Lemma lem8035184 {M N : Type'} (t : type30 N) (s : type30 M) : term124 M N t s.
Proof. exact (@lem8034203 M N t s (@lem8035182 M N t s)). Qed.
Lemma lem8035185 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term125 M N t s) : False.
Proof. exact (@lem8035184 M N t s (@lem8034187 M N t s h1)). Qed.
Lemma lem8035186 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term125 M N t s) : (term125 M N t s) = False.
Proof. exact (prop_ext (fun h2 : term125 M N t s => @lem8035185 M N t s h1) (fun h2 : False => @lem8034187 M N t s h1)). Qed.
Lemma lem8035187 {M N : Type'} (t : type30 N) (s : type30 M) (h1 : term125 M N t s) : False.
Proof. exact (EQ_MP (@lem8035186 M N t s h1) (@lem8034187 M N t s h1)). Qed.
Lemma lem8035188 {M N : Type'} (t : type30 N) (s : type30 M) : term124 M N t s.
Proof. exact (fun h0 : term125 M N t s => @lem8035187 M N t s h0). Qed.
Lemma lem8035189 {M N : Type'} (t : type30 N) (s : type30 M) : term122 M N t s.
Proof. exact (EQ_MP (@lem8034186 M N t s) (@lem8035188 M N t s)). Qed.
Lemma lem8035190 {M N : Type'} (t : type30 N) (s : type30 M) : term103 M N t s.
Proof. exact (EQ_MP (@lem8034182 M N t s) (@lem8035189 M N t s)). Qed.
Lemma lem8035191 {M N : Type'} (t : type30 N) (s : type30 M) : term102 M N t s.
Proof. exact (EQ_MP (@lem8034076 M N t s) (@lem8035190 M N t s)). Qed.
Lemma lem8035192 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term40 N t) : term98 M N t s.
Proof. exact (@lem8035191 M N t s (@lem8033775 N t h1)). Qed.
Lemma lem8035193 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term40 N t) : term63 M N t s.
Proof. exact (EQ_MP (@lem8034017 M N t s) (@lem8035192 M N s t h1)). Qed.
Lemma lem8035194 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term40 N t) : term54 M N t s.
Proof. exact (EQ_MP (@lem8033927 M N t s) (@lem8035193 M N s t h1)). Qed.
Lemma lem8035197 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term40 N t) : (term26 M N s t) = s.
Proof. exact (EQ_MP (@lem8033901 M N t s) (@lem8035194 M N s t h1)). Qed.
Lemma lem8035198 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term40 N t) : (term40 N t) = ((term26 M N s t) = s).
Proof. exact (prop_ext (fun h2 : term40 N t => @lem8035197 M N s t h1) (fun h2 : (term26 M N s t) = s => @lem8033775 N t h1)). Qed.
Lemma lem8035199 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : term40 N t) : (term26 M N s t) = s.
Proof. exact (EQ_MP (@lem8035198 M N s t h1) (@lem8033775 N t h1)). Qed.
Lemma lem8035200 {M N : Type'} (t : type30 N) (s : type30 M) : term29 M N t s.
Proof. exact (fun h0 : term40 N t => @lem8035199 M N s t h0). Qed.
Lemma lem8035201 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (term26 M N s t) = (@EMPTY (cart real M)).
Proof. exact (EQ_MP (@lem8033828 M N s t h1) (@lem0)). Qed.
Lemma lem8035202 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (t = (@EMPTY (cart real N))) = ((term26 M N s t) = (@EMPTY (cart real M))).
Proof. exact (prop_ext (fun h2 : t = (@EMPTY (cart real N)) => @lem8035201 M N s t h1) (fun h2 : (term26 M N s t) = (@EMPTY (cart real M)) => @lem8033758 N t h1)). Qed.
Lemma lem8035203 {M N : Type'} (s : type30 M) (t : type30 N) (h1 : t = (@EMPTY (cart real N))) : (term26 M N s t) = (@EMPTY (cart real M)).
Proof. exact (EQ_MP (@lem8035202 M N s t h1) (@lem8033758 N t h1)). Qed.
Lemma lem8035204 {M N : Type'} (s : type30 M) (t : type30 N) : term33 M N s t.
Proof. exact (fun h0 : t = (@EMPTY (cart real N)) => @lem8035203 M N s t h0). Qed.
Lemma lem8035205 {M N : Type'} (t : type30 N) (s : type30 M) : term36 M N t s.
Proof. exact (conj (@lem8035204 M N s t) (@lem8035200 M N t s)). Qed.
Lemma lem8035206 {M N : Type'} (t : type30 N) (s : type30 M) : (term26 M N s t) = (term37 M N t s).
Proof. exact (EQ_MP (@lem8033757 M N t s) (@lem8035205 M N t s)). Qed.
Lemma lem8035211 {M N : Type'} (s : type30 M) : term342 M N s.
Proof. exact (fun t : type30 N => @lem8035206 M N t s). Qed.
Lemma lem8035216 {M N : Type'} : term343 M N.
Proof. exact (fun s : type30 M => @lem8035211 M N s). Qed.
