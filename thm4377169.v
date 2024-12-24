Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4377169_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm4372190_spec.
Require Import thm4372272_spec.
Lemma lem4374858 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4374859 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4374860 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4374859 t1) (@lem4374858 t1)). Qed.
Lemma lem4374861 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4374860 t1 t2). Qed.
Lemma lem4374862 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4374863 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4374862 t1 t2) (@lem4374861 t1 t2)). Qed.
Lemma lem4374864 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4374863 t1 t2 t3). Qed.
Lemma lem4374865 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4374866 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4374865 t1 t2 t3) (@lem4374864 t1 t2 t3)). Qed.
Lemma lem4374867 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4374866 t1 t2 t3)). Qed.
Lemma lem4374868 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term7 _104907 f) (h2 : term7 _104908 g) : term8 _104907 _104908 g f.
Proof. exact (conj (@lem4372272 _104908 g h2) (@lem4372190 _104907 f h1)). Qed.
Lemma lem4374876 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4374877 {_104908 : Type'} (s : type686 _104908) (t : type686 _104908) : (s = t) = (term10 _104908 s t).
Proof. exact (@lem4374876 (_104908 -> Prop) s t). Qed.
Lemma lem4374878 {_104908 : Type'} (g : type686 _104908) : (g = (@EMPTY (_104908 -> Prop))) = (term11 _104908 g).
Proof. exact (@lem4374877 _104908 g (@EMPTY (_104908 -> Prop))). Qed.
Lemma lem4374887 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4374888 {_104908 : Type'} (g : type686 _104908) : (term7 _104908 g) = (term12 _104908 g).
Proof. exact (MK_COMB (@lem4374887) (@lem4374878 _104908 g)). Qed.
Lemma lem4374889 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374890 {_104908 : Type'} (g : type686 _104908) : (term13 _104908 g) = (term14 _104908 g).
Proof. exact (MK_COMB (@lem4374889) (@lem4374888 _104908 g)). Qed.
Lemma lem4374894 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term9 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem4374895 {_104907 : Type'} (s : type686 _104907) (t : type686 _104907) : (s = t) = (term10 _104907 s t).
Proof. exact (@lem4374894 (_104907 -> Prop) s t). Qed.
Lemma lem4374896 {_104907 : Type'} (f : type686 _104907) : (f = (@EMPTY (_104907 -> Prop))) = (term11 _104907 f).
Proof. exact (@lem4374895 _104907 f (@EMPTY (_104907 -> Prop))). Qed.
Lemma lem4374905 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4374906 {_104907 : Type'} (f : type686 _104907) : (term7 _104907 f) = (term12 _104907 f).
Proof. exact (MK_COMB (@lem4374905) (@lem4374896 _104907 f)). Qed.
Lemma lem4374907 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term8 _104907 _104908 g f) = (term15 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374890 _104908 g) (@lem4374906 _104907 f)). Qed.
Lemma lem4374910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4374911 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term16 _104907 _104908 g f) = (term17 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374910) (@lem4374907 _104907 _104908 g f)). Qed.
Lemma lem4374940 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term18 _104907 _104908 f g) = (term18 _104907 _104908 f g).
Proof. exact (eq_refl (term18 _104907 _104908 f g)). Qed.
Lemma lem4374941 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term19 _104907 _104908 f g) = (term20 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4374911 _104907 _104908 g f) (@lem4374940 _104907 _104908 f g)). Qed.
Lemma lem4374944 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term20 _104907 _104908 f g) = (term19 _104907 _104908 f g).
Proof. exact (SYM (@lem4374941 _104907 _104908 f g)). Qed.
Lemma lem4374956 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374957 {_104908 : Type'} (P : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x P) = (P x).
Proof. exact (@lem4374956 (_104908 -> Prop) P x). Qed.
Lemma lem4374958 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x g) = (g x).
Proof. exact (@lem4374957 _104908 g x). Qed.
Lemma lem4374959 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374960 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term21 _104908 x g) = (term22 _104908 g x).
Proof. exact (MK_COMB (@lem4374959) (@lem4374958 _104908 g x)). Qed.
Lemma lem4374962 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374963 {_104908 : Type'} (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop))) = False.
Proof. exact (@lem4374962 (_104908 -> Prop) x). Qed.
Lemma lem4374964 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : ((@IN (_104908 -> Prop) x g) = (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop)))) = ((g x) = False).
Proof. exact (MK_COMB (@lem4374960 _104908 g x) (@lem4374963 _104908 x)). Qed.
Lemma lem4374966 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4374967 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : ((g x) = False) = (term23 _104908 g x).
Proof. exact (@lem4374966 (g x)). Qed.
Lemma lem4374968 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : ((@IN (_104908 -> Prop) x g) = (@IN (_104908 -> Prop) x (@EMPTY (_104908 -> Prop)))) = (term23 _104908 g x).
Proof. exact (TRANS (@lem4374964 _104908 g x) (@lem4374967 _104908 g x)). Qed.
Lemma lem4374969 {_104908 : Type'} (g : type686 _104908) : (term24 _104908 g) = (term25 _104908 g).
Proof. exact (fun_ext (fun x : _104908 -> Prop => @lem4374968 _104908 g x)). Qed.
Lemma lem4374970 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4374971 {_104908 : Type'} (g : type686 _104908) : (term11 _104908 g) = (term26 _104908 g).
Proof. exact (MK_COMB (@lem4374970 _104908) (@lem4374969 _104908 g)). Qed.
Lemma lem4374976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4374977 {_104908 : Type'} (g : type686 _104908) : (term12 _104908 g) = (term27 _104908 g).
Proof. exact (MK_COMB (@lem4374976) (@lem4374971 _104908 g)). Qed.
Lemma lem4374978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4374979 {_104908 : Type'} (g : type686 _104908) : (term14 _104908 g) = (term28 _104908 g).
Proof. exact (MK_COMB (@lem4374978) (@lem4374977 _104908 g)). Qed.
Lemma lem4374987 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4374988 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4374987 (_104907 -> Prop) P x). Qed.
Lemma lem4374989 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x f) = (f x).
Proof. exact (@lem4374988 _104907 f x). Qed.
Lemma lem4374990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4374991 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term21 _104907 x f) = (term22 _104907 f x).
Proof. exact (MK_COMB (@lem4374990) (@lem4374989 _104907 f x)). Qed.
Lemma lem4374993 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem4374994 {_104907 : Type'} (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop))) = False.
Proof. exact (@lem4374993 (_104907 -> Prop) x). Qed.
Lemma lem4374995 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((@IN (_104907 -> Prop) x f) = (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem4374991 _104907 f x) (@lem4374994 _104907 x)). Qed.
Lemma lem4374997 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem4374998 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((f x) = False) = (term23 _104907 f x).
Proof. exact (@lem4374997 (f x)). Qed.
Lemma lem4374999 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : ((@IN (_104907 -> Prop) x f) = (@IN (_104907 -> Prop) x (@EMPTY (_104907 -> Prop)))) = (term23 _104907 f x).
Proof. exact (TRANS (@lem4374995 _104907 f x) (@lem4374998 _104907 f x)). Qed.
Lemma lem4375000 {_104907 : Type'} (f : type686 _104907) : (term24 _104907 f) = (term25 _104907 f).
Proof. exact (fun_ext (fun x : _104907 -> Prop => @lem4374999 _104907 f x)). Qed.
Lemma lem4375001 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375002 {_104907 : Type'} (f : type686 _104907) : (term11 _104907 f) = (term26 _104907 f).
Proof. exact (MK_COMB (@lem4375001 _104907) (@lem4375000 _104907 f)). Qed.
Lemma lem4375007 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375008 {_104907 : Type'} (f : type686 _104907) : (term12 _104907 f) = (term27 _104907 f).
Proof. exact (MK_COMB (@lem4375007) (@lem4375002 _104907 f)). Qed.
Lemma lem4375009 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term15 _104907 _104908 g f) = (term29 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4374979 _104908 g) (@lem4375008 _104907 f)). Qed.
Lemma lem4375012 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4375013 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term17 _104907 _104908 g f) = (term30 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4375012) (@lem4375009 _104907 _104908 g f)). Qed.
Lemma lem4375027 {A : Type'} (s : type686 A) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4375028 {_104907 : Type'} (s : type686 _104907) (x : _104907) : (term31 _104907 x s) = (term32 _104907 s x).
Proof. exact (@lem4375027 _104907 s x). Qed.
Lemma lem4375029 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term31 _104907 p1 f) = (term32 _104907 f p1).
Proof. exact (@lem4375028 _104907 f p1). Qed.
Lemma lem4375037 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375038 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4375037 (_104907 -> Prop) P x). Qed.
Lemma lem4375039 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (@IN (_104907 -> Prop) t f) = (f t).
Proof. exact (@lem4375038 _104907 f t). Qed.
Lemma lem4375040 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4375041 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (term33 _104907 t f) = (term34 _104907 f t).
Proof. exact (MK_COMB (@lem4375040) (@lem4375039 _104907 f t)). Qed.
Lemma lem4375043 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375044 {_104907 : Type'} (P : _104907 -> Prop) (x : _104907) : (@IN _104907 x P) = (P x).
Proof. exact (@lem4375043 _104907 P x). Qed.
Lemma lem4375045 {_104907 : Type'} (t : _104907 -> Prop) (p1 : _104907) : (@IN _104907 p1 t) = (t p1).
Proof. exact (@lem4375044 _104907 t p1). Qed.
Lemma lem4375046 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term35 _104907 f p1 t) = (term36 _104907 f t p1).
Proof. exact (MK_COMB (@lem4375041 _104907 f t) (@lem4375045 _104907 t p1)). Qed.
Lemma lem4375049 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term37 _104907 f p1) = (term38 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375046 _104907 f t p1)). Qed.
Lemma lem4375050 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375051 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term32 _104907 f p1) = (term39 _104907 f p1).
Proof. exact (MK_COMB (@lem4375050 _104907) (@lem4375049 _104907 f p1)). Qed.
Lemma lem4375056 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term31 _104907 p1 f) = (term39 _104907 f p1).
Proof. exact (TRANS (@lem4375029 _104907 f p1) (@lem4375051 _104907 f p1)). Qed.
Lemma lem4375057 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375058 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term40 _104907 p1 f) = (term41 _104907 f p1).
Proof. exact (MK_COMB (@lem4375057) (@lem4375056 _104907 f p1)). Qed.
Lemma lem4375060 {A : Type'} (s : type686 A) (x : A) : (term31 A x s) = (term32 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem4375061 {_104908 : Type'} (s : type686 _104908) (x : _104908) : (term31 _104908 x s) = (term32 _104908 s x).
Proof. exact (@lem4375060 _104908 s x). Qed.
Lemma lem4375062 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term31 _104908 p2 g) = (term32 _104908 g p2).
Proof. exact (@lem4375061 _104908 g p2). Qed.
Lemma lem4375070 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375071 {_104908 : Type'} (P : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x P) = (P x).
Proof. exact (@lem4375070 (_104908 -> Prop) P x). Qed.
Lemma lem4375072 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (@IN (_104908 -> Prop) t g) = (g t).
Proof. exact (@lem4375071 _104908 g t). Qed.
Lemma lem4375073 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4375074 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term33 _104908 t g) = (term34 _104908 g t).
Proof. exact (MK_COMB (@lem4375073) (@lem4375072 _104908 g t)). Qed.
Lemma lem4375076 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375077 {_104908 : Type'} (P : _104908 -> Prop) (x : _104908) : (@IN _104908 x P) = (P x).
Proof. exact (@lem4375076 _104908 P x). Qed.
Lemma lem4375078 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (@IN _104908 p2 t) = (t p2).
Proof. exact (@lem4375077 _104908 t p2). Qed.
Lemma lem4375079 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term35 _104908 g p2 t) = (term36 _104908 g t p2).
Proof. exact (MK_COMB (@lem4375074 _104908 g t) (@lem4375078 _104908 t p2)). Qed.
Lemma lem4375082 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term37 _104908 g p2) = (term38 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375079 _104908 g t p2)). Qed.
Lemma lem4375083 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375084 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term32 _104908 g p2) = (term39 _104908 g p2).
Proof. exact (MK_COMB (@lem4375083 _104908) (@lem4375082 _104908 g p2)). Qed.
Lemma lem4375089 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term31 _104908 p2 g) = (term39 _104908 g p2).
Proof. exact (TRANS (@lem4375062 _104908 g p2) (@lem4375084 _104908 g p2)). Qed.
Lemma lem4375090 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term42 _104907 _104908 p1 f p2 g) = (term43 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375058 _104907 f p1) (@lem4375089 _104908 g p2)). Qed.
Lemma lem4375093 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375094 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term44 _104907 _104908 p1 f p2 g) = (term45 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375093) (@lem4375090 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375108 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375109 {_104907 : Type'} (P : type686 _104907) (x : _104907 -> Prop) : (@IN (_104907 -> Prop) x P) = (P x).
Proof. exact (@lem4375108 (_104907 -> Prop) P x). Qed.
Lemma lem4375110 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (@IN (_104907 -> Prop) s f) = (f s).
Proof. exact (@lem4375109 _104907 f s). Qed.
Lemma lem4375111 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375112 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term46 _104907 s f) = (term47 _104907 f s).
Proof. exact (MK_COMB (@lem4375111) (@lem4375110 _104907 f s)). Qed.
Lemma lem4375114 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375115 {_104908 : Type'} (P : type686 _104908) (x : _104908 -> Prop) : (@IN (_104908 -> Prop) x P) = (P x).
Proof. exact (@lem4375114 (_104908 -> Prop) P x). Qed.
Lemma lem4375116 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (@IN (_104908 -> Prop) t g) = (g t).
Proof. exact (@lem4375115 _104908 g t). Qed.
Lemma lem4375117 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term48 _104907 _104908 s f t g) = (term49 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4375112 _104907 f s) (@lem4375116 _104908 g t)). Qed.
Lemma lem4375120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4375121 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term50 _104907 _104908 s f t g) = (term51 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4375120) (@lem4375117 _104907 _104908 f s g t)). Qed.
Lemma lem4375125 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375126 {_104907 : Type'} (P : _104907 -> Prop) (x : _104907) : (@IN _104907 x P) = (P x).
Proof. exact (@lem4375125 _104907 P x). Qed.
Lemma lem4375127 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (@IN _104907 p1 s) = (s p1).
Proof. exact (@lem4375126 _104907 s p1). Qed.
Lemma lem4375128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375129 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term52 _104907 p1 s) = (term53 _104907 s p1).
Proof. exact (MK_COMB (@lem4375128) (@lem4375127 _104907 s p1)). Qed.
Lemma lem4375131 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem4375132 {_104908 : Type'} (P : _104908 -> Prop) (x : _104908) : (@IN _104908 x P) = (P x).
Proof. exact (@lem4375131 _104908 P x). Qed.
Lemma lem4375133 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (@IN _104908 p2 t) = (t p2).
Proof. exact (@lem4375132 _104908 t p2). Qed.
Lemma lem4375134 {_104907 _104908 : Type'} (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term54 _104907 _104908 p1 s p2 t) = (term55 _104907 _104908 s p1 t p2).
Proof. exact (MK_COMB (@lem4375129 _104907 s p1) (@lem4375133 _104908 t p2)). Qed.
Lemma lem4375137 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term56 _104907 _104908 f g p1 s p2 t) = (term57 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4375121 _104907 _104908 f s g t) (@lem4375134 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4375140 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term58 _104907 _104908 f g p1 s p2) = (term59 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375137 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375141 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375142 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term60 _104907 _104908 f g p1 s p2) = (term61 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375141 _104908) (@lem4375140 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375147 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term62 _104907 _104908 f g p1 p2) = (term63 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375142 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375148 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375149 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term64 _104907 _104908 f g p1 p2) = (term65 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375148 _104907) (@lem4375147 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375154 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term42 _104907 _104908 p1 f p2 g) = (term64 _104907 _104908 f g p1 p2)) = ((term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4375094 _104907 _104908 f p1 g p2) (@lem4375149 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375157 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) : (term66 _104907 _104908 f g p1) = (term67 _104907 _104908 f g p1).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4375154 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375158 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4375159 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) : (term68 _104907 _104908 f g p1) = (term69 _104907 _104908 f g p1).
Proof. exact (MK_COMB (@lem4375158 _104908) (@lem4375157 _104907 _104908 f g p1)). Qed.
Lemma lem4375164 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term70 _104907 _104908 f g) = (term71 _104907 _104908 f g).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4375159 _104907 _104908 f g p1)). Qed.
Lemma lem4375165 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4375166 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term18 _104907 _104908 f g) = (term72 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4375165 _104907) (@lem4375164 _104907 _104908 f g)). Qed.
Lemma lem4375171 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term20 _104907 _104908 f g) = (term73 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4375013 _104907 _104908 g f) (@lem4375166 _104907 _104908 f g)). Qed.
Lemma lem4375174 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term73 _104907 _104908 f g) = (term20 _104907 _104908 f g).
Proof. exact (SYM (@lem4375171 _104907 _104908 f g)). Qed.
Lemma lem4375176 (p : Prop) : p = (term74 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4375177 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term73 _104907 _104908 f g) = (term75 _104907 _104908 f g).
Proof. exact (@lem4375176 (term73 _104907 _104908 f g)). Qed.
Lemma lem4375178 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term75 _104907 _104908 f g) = (term73 _104907 _104908 f g).
Proof. exact (SYM (@lem4375177 _104907 _104908 f g)). Qed.
Lemma lem4375179 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term76 _104907 _104908 f g) : term76 _104907 _104908 f g.
Proof. exact (h1). Qed.
Lemma lem4375182 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term75 _104907 _104908 f g) : term75 _104907 _104908 f g.
Proof. exact (h1). Qed.
Lemma lem4375183 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term77 _104907 _104908 f g.
Proof. exact (fun h0 : term75 _104907 _104908 f g => @lem4375182 _104907 _104908 f g h0). Qed.
Lemma lem4375184 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term77 _104907 _104908 f g) : term77 _104907 _104908 f g.
Proof. exact (h1). Qed.
Lemma lem4375185 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term75 _104907 _104908 f g) : term75 _104907 _104908 f g.
Proof. exact (h1). Qed.
Lemma lem4375186 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term75 _104907 _104908 f g) (h2 : term77 _104907 _104908 f g) : term75 _104907 _104908 f g.
Proof. exact (@lem4375184 _104907 _104908 f g h2 (@lem4375185 _104907 _104908 f g h1)). Qed.
Lemma lem4375187 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term75 _104907 _104908 f g) : term78 _104907 _104908 f g.
Proof. exact (fun h0 : term77 _104907 _104908 f g => @lem4375186 _104907 _104908 f g h1 h0). Qed.
Lemma lem4375188 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term77 _104907 _104908 f g) : term77 _104907 _104908 f g.
Proof. exact (h1). Qed.
Lemma lem4375189 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term75 _104907 _104908 f g) (h2 : term77 _104907 _104908 f g) : term75 _104907 _104908 f g.
Proof. exact (@lem4375187 _104907 _104908 f g h1 (@lem4375188 _104907 _104908 f g h2)). Qed.
Lemma lem4375190 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term77 _104907 _104908 f g) : term77 _104907 _104908 f g.
Proof. exact (fun h0 : term75 _104907 _104908 f g => @lem4375189 _104907 _104908 f g h0 h1). Qed.
Lemma lem4375191 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term79 _104907 _104908 f g.
Proof. exact (fun h0 : term77 _104907 _104908 f g => @lem4375190 _104907 _104908 f g h0). Qed.
Lemma lem4375194 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term77 _104907 _104908 f g.
Proof. exact (@lem4375191 _104907 _104908 f g (@lem4375183 _104907 _104908 f g)). Qed.
Lemma lem4375195 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term77 _104907 _104908 f g.
Proof. exact (@lem4375194 _104907 _104908 f g). Qed.
Lemma lem4375205 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4375206 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term75 _104907 _104908 f g) = (term80 _104907 _104908 f g).
Proof. exact (@lem4375205 (term76 _104907 _104908 f g)). Qed.
Lemma lem4375208 (t : Prop) : (term81 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4375209 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term80 _104907 _104908 f g) = (term73 _104907 _104908 f g).
Proof. exact (@lem4375208 (term73 _104907 _104908 f g)). Qed.
Lemma lem4375212 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term75 _104907 _104908 f g) = (term73 _104907 _104908 f g).
Proof. exact (TRANS (@lem4375206 _104907 _104908 f g) (@lem4375209 _104907 _104908 f g)). Qed.
Lemma lem4375259 {_104907 _104908 : Type'} (g : type686 _104908) : (term82 _104907 _104908 g) = (term83 _104907 _104908 g).
Proof. exact (fun_ext (fun f : type686 _104907 => @lem4375212 _104907 _104908 f g)). Qed.
Lemma lem4375260 {_104907 : Type'} : (@all ((_104907 -> Prop) -> Prop)) = (@all ((_104907 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104907 -> Prop) -> Prop))). Qed.
Lemma lem4375261 {_104907 _104908 : Type'} (g : type686 _104908) : (term84 _104907 _104908 g) = (term85 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4375260 _104907) (@lem4375259 _104907 _104908 g)). Qed.
Lemma lem4375266 {_104907 _104908 : Type'} : (term86 _104907 _104908) = (term87 _104907 _104908).
Proof. exact (fun_ext (fun g : type686 _104908 => @lem4375261 _104907 _104908 g)). Qed.
Lemma lem4375267 {_104908 : Type'} : (@all ((_104908 -> Prop) -> Prop)) = (@all ((_104908 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104908 -> Prop) -> Prop))). Qed.
Lemma lem4375276 {_104907 _104908 : Type'} : (term88 _104907 _104908) = (term89 _104907 _104908).
Proof. exact (MK_COMB (@lem4375267 _104908) (@lem4375266 _104907 _104908)). Qed.
Lemma lem4375289 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term57 _104907 _104908 f g s p1 t p2) = (term57 _104907 _104908 f g s p1 t p2).
Proof. exact (eq_refl (term57 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375290 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term59 _104907 _104908 f g s p1 p2) = (term59 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375289 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375291 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375292 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term61 _104907 _104908 f g s p1 p2) = (term61 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375291 _104908) (@lem4375290 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375293 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term63 _104907 _104908 f g p1 p2) = (term63 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375292 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375294 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375295 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term65 _104907 _104908 f g p1 p2) = (term65 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375294 _104907) (@lem4375293 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375300 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term36 _104908 g t p2) = (term36 _104908 g t p2).
Proof. exact (eq_refl (term36 _104908 g t p2)). Qed.
Lemma lem4375301 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term38 _104908 g p2) = (term38 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375300 _104908 g t p2)). Qed.
Lemma lem4375302 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375303 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term39 _104908 g p2) = (term39 _104908 g p2).
Proof. exact (MK_COMB (@lem4375302 _104908) (@lem4375301 _104908 g p2)). Qed.
Lemma lem4375308 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term36 _104907 f t p1) = (term36 _104907 f t p1).
Proof. exact (eq_refl (term36 _104907 f t p1)). Qed.
Lemma lem4375309 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term38 _104907 f p1) = (term38 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375308 _104907 f t p1)). Qed.
Lemma lem4375310 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375311 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term39 _104907 f p1) = (term39 _104907 f p1).
Proof. exact (MK_COMB (@lem4375310 _104907) (@lem4375309 _104907 f p1)). Qed.
Lemma lem4375312 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375313 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term41 _104907 f p1) = (term41 _104907 f p1).
Proof. exact (MK_COMB (@lem4375312) (@lem4375311 _104907 f p1)). Qed.
Lemma lem4375314 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term43 _104907 _104908 f p1 g p2) = (term43 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375313 _104907 f p1) (@lem4375303 _104908 g p2)). Qed.
Lemma lem4375315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375316 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term45 _104907 _104908 f p1 g p2) = (term45 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375315) (@lem4375314 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375317 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2)) = ((term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4375316 _104907 _104908 f p1 g p2) (@lem4375295 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375318 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) : (term67 _104907 _104908 f g p1) = (term67 _104907 _104908 f g p1).
Proof. exact (fun_ext (fun p2 : _104908 => @lem4375317 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375319 {_104908 : Type'} : (@all _104908) = (@all _104908).
Proof. exact (eq_refl (@all _104908)). Qed.
Lemma lem4375320 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) : (term69 _104907 _104908 f g p1) = (term69 _104907 _104908 f g p1).
Proof. exact (MK_COMB (@lem4375319 _104908) (@lem4375318 _104907 _104908 f g p1)). Qed.
Lemma lem4375321 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term71 _104907 _104908 f g) = (term71 _104907 _104908 f g).
Proof. exact (fun_ext (fun p1 : _104907 => @lem4375320 _104907 _104908 f g p1)). Qed.
Lemma lem4375322 {_104907 : Type'} : (@all _104907) = (@all _104907).
Proof. exact (eq_refl (@all _104907)). Qed.
Lemma lem4375323 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term72 _104907 _104908 f g) = (term72 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4375322 _104907) (@lem4375321 _104907 _104908 f g)). Qed.
Lemma lem4375326 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term23 _104907 f x) = (term23 _104907 f x).
Proof. exact (eq_refl (term23 _104907 f x)). Qed.
Lemma lem4375327 {_104907 : Type'} (f : type686 _104907) : (term25 _104907 f) = (term25 _104907 f).
Proof. exact (fun_ext (fun x : _104907 -> Prop => @lem4375326 _104907 f x)). Qed.
Lemma lem4375328 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375329 {_104907 : Type'} (f : type686 _104907) : (term26 _104907 f) = (term26 _104907 f).
Proof. exact (MK_COMB (@lem4375328 _104907) (@lem4375327 _104907 f)). Qed.
Lemma lem4375330 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375331 {_104907 : Type'} (f : type686 _104907) : (term27 _104907 f) = (term27 _104907 f).
Proof. exact (MK_COMB (@lem4375330) (@lem4375329 _104907 f)). Qed.
Lemma lem4375334 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term23 _104908 g x) = (term23 _104908 g x).
Proof. exact (eq_refl (term23 _104908 g x)). Qed.
Lemma lem4375335 {_104908 : Type'} (g : type686 _104908) : (term25 _104908 g) = (term25 _104908 g).
Proof. exact (fun_ext (fun x : _104908 -> Prop => @lem4375334 _104908 g x)). Qed.
Lemma lem4375336 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375337 {_104908 : Type'} (g : type686 _104908) : (term26 _104908 g) = (term26 _104908 g).
Proof. exact (MK_COMB (@lem4375336 _104908) (@lem4375335 _104908 g)). Qed.
Lemma lem4375338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375339 {_104908 : Type'} (g : type686 _104908) : (term27 _104908 g) = (term27 _104908 g).
Proof. exact (MK_COMB (@lem4375338) (@lem4375337 _104908 g)). Qed.
Lemma lem4375340 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375341 {_104908 : Type'} (g : type686 _104908) : (term28 _104908 g) = (term28 _104908 g).
Proof. exact (MK_COMB (@lem4375340) (@lem4375339 _104908 g)). Qed.
Lemma lem4375342 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term29 _104907 _104908 g f) = (term29 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4375341 _104908 g) (@lem4375331 _104907 f)). Qed.
Lemma lem4375343 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4375344 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term30 _104907 _104908 g f) = (term30 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4375343) (@lem4375342 _104907 _104908 g f)). Qed.
Lemma lem4375345 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term73 _104907 _104908 f g) = (term73 _104907 _104908 f g).
Proof. exact (MK_COMB (@lem4375344 _104907 _104908 g f) (@lem4375323 _104907 _104908 f g)). Qed.
Lemma lem4375346 {_104907 _104908 : Type'} (g : type686 _104908) : (term83 _104907 _104908 g) = (term83 _104907 _104908 g).
Proof. exact (fun_ext (fun f : type686 _104907 => @lem4375345 _104907 _104908 f g)). Qed.
Lemma lem4375347 {_104907 : Type'} : (@all ((_104907 -> Prop) -> Prop)) = (@all ((_104907 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104907 -> Prop) -> Prop))). Qed.
Lemma lem4375348 {_104907 _104908 : Type'} (g : type686 _104908) : (term85 _104907 _104908 g) = (term85 _104907 _104908 g).
Proof. exact (MK_COMB (@lem4375347 _104907) (@lem4375346 _104907 _104908 g)). Qed.
Lemma lem4375349 {_104907 _104908 : Type'} : (term87 _104907 _104908) = (term87 _104907 _104908).
Proof. exact (fun_ext (fun g : type686 _104908 => @lem4375348 _104907 _104908 g)). Qed.
Lemma lem4375350 {_104908 : Type'} : (@all ((_104908 -> Prop) -> Prop)) = (@all ((_104908 -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((_104908 -> Prop) -> Prop))). Qed.
Lemma lem4375351 {_104907 _104908 : Type'} : (term89 _104907 _104908) = (term89 _104907 _104908).
Proof. exact (MK_COMB (@lem4375350 _104908) (@lem4375349 _104907 _104908)). Qed.
Lemma lem4375430 {_104907 _104908 : Type'} : (term88 _104907 _104908) = (term89 _104907 _104908).
Proof. exact (TRANS (@lem4375276 _104907 _104908) (@lem4375351 _104907 _104908)). Qed.
Lemma lem4375431 {_104907 _104908 : Type'} : (term89 _104907 _104908) = (term88 _104907 _104908).
Proof. exact (SYM (@lem4375430 _104907 _104908)). Qed.
Lemma lem4375432 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term29 _104907 _104908 g f) : term29 _104907 _104908 g f.
Proof. exact (h1). Qed.
Lemma lem4375434 (p : Prop) : p = (term74 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4375435 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2)) = (term90 _104907 _104908 f g p1 p2).
Proof. exact (@lem4375434 ((term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2))). Qed.
Lemma lem4375436 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term90 _104907 _104908 f g p1 p2) = ((term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2)).
Proof. exact (SYM (@lem4375435 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375437 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term91 _104907 _104908 f g p1 p2) : term91 _104907 _104908 f g p1 p2.
Proof. exact (h1). Qed.
Lemma lem4375440 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term92 _104908 g x) = (g x).
Proof. exact (@lem16933 (g x)). Qed.
Lemma lem4375441 {_104908 : Type'} (P : type686 _104908) : (term93 _104908 P) = (term94 _104908 P).
Proof. exact (@lem18392 (_104908 -> Prop) P). Qed.
Lemma lem4375442 {_104908 : Type'} (g : type686 _104908) : (term27 _104908 g) = (term95 _104908 g).
Proof. exact (@lem4375441 _104908 (term25 _104908 g)). Qed.
Lemma lem4375443 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term96 _104908 g x) = (term23 _104908 g x).
Proof. exact (eq_refl (term96 _104908 g x)). Qed.
Lemma lem4375444 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375445 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term97 _104908 g x) = (term92 _104908 g x).
Proof. exact (MK_COMB (@lem4375444) (@lem4375443 _104908 g x)). Qed.
Lemma lem4375446 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term97 _104908 g x) = (g x).
Proof. exact (TRANS (@lem4375445 _104908 g x) (@lem4375440 _104908 g x)). Qed.
Lemma lem4375447 {_104908 : Type'} (g : type686 _104908) : (term98 _104908 g) = (term99 _104908 g).
Proof. exact (fun_ext (fun x : _104908 -> Prop => @lem4375446 _104908 g x)). Qed.
Lemma lem4375448 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375449 {_104908 : Type'} (g : type686 _104908) : (term95 _104908 g) = (term100 _104908 g).
Proof. exact (MK_COMB (@lem4375448 _104908) (@lem4375447 _104908 g)). Qed.
Lemma lem4375450 {_104908 : Type'} (g : type686 _104908) : (term27 _104908 g) = (term100 _104908 g).
Proof. exact (TRANS (@lem4375442 _104908 g) (@lem4375449 _104908 g)). Qed.
Lemma lem4375453 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term92 _104907 f x) = (f x).
Proof. exact (@lem16933 (f x)). Qed.
Lemma lem4375454 {_104907 : Type'} (P : type686 _104907) : (term93 _104907 P) = (term94 _104907 P).
Proof. exact (@lem18392 (_104907 -> Prop) P). Qed.
Lemma lem4375455 {_104907 : Type'} (f : type686 _104907) : (term27 _104907 f) = (term95 _104907 f).
Proof. exact (@lem4375454 _104907 (term25 _104907 f)). Qed.
Lemma lem4375456 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term96 _104907 f x) = (term23 _104907 f x).
Proof. exact (eq_refl (term96 _104907 f x)). Qed.
Lemma lem4375457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375458 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term97 _104907 f x) = (term92 _104907 f x).
Proof. exact (MK_COMB (@lem4375457) (@lem4375456 _104907 f x)). Qed.
Lemma lem4375459 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (term97 _104907 f x) = (f x).
Proof. exact (TRANS (@lem4375458 _104907 f x) (@lem4375453 _104907 f x)). Qed.
Lemma lem4375460 {_104907 : Type'} (f : type686 _104907) : (term98 _104907 f) = (term99 _104907 f).
Proof. exact (fun_ext (fun x : _104907 -> Prop => @lem4375459 _104907 f x)). Qed.
Lemma lem4375461 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375462 {_104907 : Type'} (f : type686 _104907) : (term95 _104907 f) = (term100 _104907 f).
Proof. exact (MK_COMB (@lem4375461 _104907) (@lem4375460 _104907 f)). Qed.
Lemma lem4375463 {_104907 : Type'} (f : type686 _104907) : (term27 _104907 f) = (term100 _104907 f).
Proof. exact (TRANS (@lem4375455 _104907 f) (@lem4375462 _104907 f)). Qed.
Lemma lem4375464 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375465 {_104908 : Type'} (g : type686 _104908) : (term28 _104908 g) = (term101 _104908 g).
Proof. exact (MK_COMB (@lem4375464) (@lem4375450 _104908 g)). Qed.
Lemma lem4375466 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term29 _104907 _104908 g f) = (term102 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4375465 _104908 g) (@lem4375463 _104907 f)). Qed.
Lemma lem4375477 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4375478 {_104908 : Type'} (P : type686 _104908) (Q : Prop) : (term105 _104908 P Q) = (term106 _104908 P Q).
Proof. exact (@lem4375477 (_104908 -> Prop) P Q). Qed.
Lemma lem4375479 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term102 _104907 _104908 g f) = (term107 _104907 _104908 g f).
Proof. exact (@lem4375478 _104908 g (term100 _104907 f)). Qed.
Lemma lem4375481 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4375482 {_104907 : Type'} (P : Prop) (Q : type686 _104907) : (term110 _104907 P Q) = (term111 _104907 P Q).
Proof. exact (@lem4375481 (_104907 -> Prop) P Q). Qed.
Lemma lem4375483 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) : (term112 _104907 _104908 g x f) = (term113 _104907 _104908 g x f).
Proof. exact (@lem4375482 _104907 (g x) f). Qed.
Lemma lem4375484 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term114 _104907 _104908 g f) = (term115 _104907 _104908 g f).
Proof. exact (fun_ext (fun x : _104908 -> Prop => @lem4375483 _104907 _104908 g x f)). Qed.
Lemma lem4375485 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375486 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term107 _104907 _104908 g f) = (term116 _104907 _104908 g f).
Proof. exact (MK_COMB (@lem4375485 _104908) (@lem4375484 _104907 _104908 g f)). Qed.
Lemma lem4375488 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term102 _104907 _104908 g f) = (term116 _104907 _104908 g f).
Proof. exact (TRANS (@lem4375479 _104907 _104908 g f) (@lem4375486 _104907 _104908 g f)). Qed.
Lemma lem4375489 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : (term29 _104907 _104908 g f) = (term116 _104907 _104908 g f).
Proof. exact (TRANS (@lem4375466 _104907 _104908 g f) (@lem4375488 _104907 _104908 g f)). Qed.
Lemma lem4375490 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term29 _104907 _104908 g f) : term116 _104907 _104908 g f.
Proof. exact (EQ_MP (@lem4375489 _104907 _104908 g f) (@lem4375432 _104907 _104908 g f h1)). Qed.
Lemma lem4375499 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term117 _104907 f t p1) = (term118 _104907 f t p1).
Proof. exact (@lem17362 (f t) (t p1)). Qed.
Lemma lem4375504 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term36 _104907 f t p1) = (term119 _104907 f t p1).
Proof. exact (@lem17265 (f t) (t p1)). Qed.
Lemma lem4375505 {_104907 : Type'} (P : type686 _104907) : (term93 _104907 P) = (term94 _104907 P).
Proof. exact (@lem18392 (_104907 -> Prop) P). Qed.
Lemma lem4375506 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term120 _104907 f p1) = (term121 _104907 f p1).
Proof. exact (@lem4375505 _104907 (term38 _104907 f p1)). Qed.
Lemma lem4375507 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term122 _104907 f p1 t) = (term36 _104907 f t p1).
Proof. exact (eq_refl (term122 _104907 f p1 t)). Qed.
Lemma lem4375508 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375509 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term123 _104907 f p1 t) = (term117 _104907 f t p1).
Proof. exact (MK_COMB (@lem4375508) (@lem4375507 _104907 f t p1)). Qed.
Lemma lem4375510 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term123 _104907 f p1 t) = (term118 _104907 f t p1).
Proof. exact (TRANS (@lem4375509 _104907 f t p1) (@lem4375499 _104907 f t p1)). Qed.
Lemma lem4375511 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term124 _104907 f p1) = (term125 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375510 _104907 f t p1)). Qed.
Lemma lem4375512 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375513 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term121 _104907 f p1) = (term126 _104907 f p1).
Proof. exact (MK_COMB (@lem4375512 _104907) (@lem4375511 _104907 f p1)). Qed.
Lemma lem4375514 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term120 _104907 f p1) = (term126 _104907 f p1).
Proof. exact (TRANS (@lem4375506 _104907 f p1) (@lem4375513 _104907 f p1)). Qed.
Lemma lem4375515 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term38 _104907 f p1) = (term127 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375504 _104907 f t p1)). Qed.
Lemma lem4375516 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375517 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term39 _104907 f p1) = (term128 _104907 f p1).
Proof. exact (MK_COMB (@lem4375516 _104907) (@lem4375515 _104907 f p1)). Qed.
Lemma lem4375526 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term117 _104908 g t p2) = (term118 _104908 g t p2).
Proof. exact (@lem17362 (g t) (t p2)). Qed.
Lemma lem4375531 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term36 _104908 g t p2) = (term119 _104908 g t p2).
Proof. exact (@lem17265 (g t) (t p2)). Qed.
Lemma lem4375532 {_104908 : Type'} (P : type686 _104908) : (term93 _104908 P) = (term94 _104908 P).
Proof. exact (@lem18392 (_104908 -> Prop) P). Qed.
Lemma lem4375533 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term120 _104908 g p2) = (term121 _104908 g p2).
Proof. exact (@lem4375532 _104908 (term38 _104908 g p2)). Qed.
Lemma lem4375534 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term122 _104908 g p2 t) = (term36 _104908 g t p2).
Proof. exact (eq_refl (term122 _104908 g p2 t)). Qed.
Lemma lem4375535 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375536 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term123 _104908 g p2 t) = (term117 _104908 g t p2).
Proof. exact (MK_COMB (@lem4375535) (@lem4375534 _104908 g t p2)). Qed.
Lemma lem4375537 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term123 _104908 g p2 t) = (term118 _104908 g t p2).
Proof. exact (TRANS (@lem4375536 _104908 g t p2) (@lem4375526 _104908 g t p2)). Qed.
Lemma lem4375538 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term124 _104908 g p2) = (term125 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375537 _104908 g t p2)). Qed.
Lemma lem4375539 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375540 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term121 _104908 g p2) = (term126 _104908 g p2).
Proof. exact (MK_COMB (@lem4375539 _104908) (@lem4375538 _104908 g p2)). Qed.
Lemma lem4375541 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term120 _104908 g p2) = (term126 _104908 g p2).
Proof. exact (TRANS (@lem4375533 _104908 g p2) (@lem4375540 _104908 g p2)). Qed.
Lemma lem4375542 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term38 _104908 g p2) = (term127 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375531 _104908 g t p2)). Qed.
Lemma lem4375543 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375544 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term39 _104908 g p2) = (term128 _104908 g p2).
Proof. exact (MK_COMB (@lem4375543 _104908) (@lem4375542 _104908 g p2)). Qed.
Lemma lem4375545 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4375546 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term129 _104907 f p1) = (term130 _104907 f p1).
Proof. exact (MK_COMB (@lem4375545) (@lem4375514 _104907 f p1)). Qed.
Lemma lem4375547 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term131 _104907 _104908 f p1 g p2) = (term132 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375546 _104907 f p1) (@lem4375541 _104908 g p2)). Qed.
Lemma lem4375548 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term133 _104907 _104908 f p1 g p2) = (term131 _104907 _104908 f p1 g p2).
Proof. exact (@lem17045 (term39 _104907 f p1) (term39 _104908 g p2)). Qed.
Lemma lem4375549 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term133 _104907 _104908 f p1 g p2) = (term132 _104907 _104908 f p1 g p2).
Proof. exact (TRANS (@lem4375548 _104907 _104908 f p1 g p2) (@lem4375547 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375550 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375551 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term41 _104907 f p1) = (term134 _104907 f p1).
Proof. exact (MK_COMB (@lem4375550) (@lem4375517 _104907 f p1)). Qed.
Lemma lem4375552 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term43 _104907 _104908 f p1 g p2) = (term135 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375551 _104907 f p1) (@lem4375544 _104908 g p2)). Qed.
Lemma lem4375561 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term136 _104907 _104908 f s g t) = (term137 _104907 _104908 f s g t).
Proof. exact (@lem17045 (f s) (g t)). Qed.
Lemma lem4375573 {_104907 _104908 : Type'} (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term138 _104907 _104908 s p1 t p2) = (term139 _104907 _104908 s p1 t p2).
Proof. exact (@lem17045 (s p1) (t p2)). Qed.
Lemma lem4375576 {_104907 _104908 : Type'} (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term55 _104907 _104908 s p1 t p2) = (term55 _104907 _104908 s p1 t p2).
Proof. exact (eq_refl (term55 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4375578 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term140 _104907 _104908 f s g t) = (term140 _104907 _104908 f s g t).
Proof. exact (eq_refl (term140 _104907 _104908 f s g t)). Qed.
Lemma lem4375579 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term141 _104907 _104908 f g s p1 t p2) = (term142 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4375578 _104907 _104908 f s g t) (@lem4375573 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4375580 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term143 _104907 _104908 f g s p1 t p2) = (term141 _104907 _104908 f g s p1 t p2).
Proof. exact (@lem17362 (term49 _104907 _104908 f s g t) (term55 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4375581 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term143 _104907 _104908 f g s p1 t p2) = (term142 _104907 _104908 f g s p1 t p2).
Proof. exact (TRANS (@lem4375580 _104907 _104908 f g s p1 t p2) (@lem4375579 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375582 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4375583 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term144 _104907 _104908 f s g t) = (term145 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4375582) (@lem4375561 _104907 _104908 f s g t)). Qed.
Lemma lem4375584 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term146 _104907 _104908 f g s p1 t p2) = (term147 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4375583 _104907 _104908 f s g t) (@lem4375576 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4375585 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term57 _104907 _104908 f g s p1 t p2) = (term146 _104907 _104908 f g s p1 t p2).
Proof. exact (@lem17265 (term49 _104907 _104908 f s g t) (term55 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4375586 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term57 _104907 _104908 f g s p1 t p2) = (term147 _104907 _104908 f g s p1 t p2).
Proof. exact (TRANS (@lem4375585 _104907 _104908 f g s p1 t p2) (@lem4375584 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375587 {_104908 : Type'} (P : type686 _104908) : (term93 _104908 P) = (term94 _104908 P).
Proof. exact (@lem18392 (_104908 -> Prop) P). Qed.
Lemma lem4375588 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term148 _104907 _104908 f g s p1 p2) = (term149 _104907 _104908 f g s p1 p2).
Proof. exact (@lem4375587 _104908 (term59 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375589 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term150 _104907 _104908 f g s p1 p2 t) = (term57 _104907 _104908 f g s p1 t p2).
Proof. exact (eq_refl (term150 _104907 _104908 f g s p1 p2 t)). Qed.
Lemma lem4375590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375591 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term151 _104907 _104908 f g s p1 p2 t) = (term143 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4375590) (@lem4375589 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375592 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term151 _104907 _104908 f g s p1 p2 t) = (term142 _104907 _104908 f g s p1 t p2).
Proof. exact (TRANS (@lem4375591 _104907 _104908 f g s p1 t p2) (@lem4375581 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375593 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term152 _104907 _104908 f g s p1 p2) = (term153 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375592 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375594 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375595 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term149 _104907 _104908 f g s p1 p2) = (term154 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375594 _104908) (@lem4375593 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375596 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term148 _104907 _104908 f g s p1 p2) = (term154 _104907 _104908 f g s p1 p2).
Proof. exact (TRANS (@lem4375588 _104907 _104908 f g s p1 p2) (@lem4375595 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375597 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term59 _104907 _104908 f g s p1 p2) = (term155 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375586 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375598 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4375599 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term61 _104907 _104908 f g s p1 p2) = (term156 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375598 _104908) (@lem4375597 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375600 {_104907 : Type'} (P : type686 _104907) : (term93 _104907 P) = (term94 _104907 P).
Proof. exact (@lem18392 (_104907 -> Prop) P). Qed.
Lemma lem4375601 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term157 _104907 _104908 f g p1 p2) = (term158 _104907 _104908 f g p1 p2).
Proof. exact (@lem4375600 _104907 (term63 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375602 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term159 _104907 _104908 f g p1 p2 s) = (term61 _104907 _104908 f g s p1 p2).
Proof. exact (eq_refl (term159 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4375603 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4375604 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term160 _104907 _104908 f g p1 p2 s) = (term148 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375603) (@lem4375602 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375605 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term160 _104907 _104908 f g p1 p2 s) = (term154 _104907 _104908 f g s p1 p2).
Proof. exact (TRANS (@lem4375604 _104907 _104908 f g s p1 p2) (@lem4375596 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375606 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term161 _104907 _104908 f g p1 p2) = (term162 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375605 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375607 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375608 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term158 _104907 _104908 f g p1 p2) = (term163 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375607 _104907) (@lem4375606 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375609 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term157 _104907 _104908 f g p1 p2) = (term163 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4375601 _104907 _104908 f g p1 p2) (@lem4375608 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375610 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term63 _104907 _104908 f g p1 p2) = (term164 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375599 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375611 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4375612 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term65 _104907 _104908 f g p1 p2) = (term165 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375611 _104907) (@lem4375610 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375613 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375614 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term166 _104907 _104908 f p1 g p2) = (term167 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375613) (@lem4375549 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375615 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term168 _104907 _104908 f g p1 p2) = (term169 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375614 _104907 _104908 f p1 g p2) (@lem4375612 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375616 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375617 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term170 _104907 _104908 f p1 g p2) = (term171 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375616) (@lem4375552 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375618 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term172 _104907 _104908 f g p1 p2) = (term173 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375617 _104907 _104908 f p1 g p2) (@lem4375609 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4375620 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term174 _104907 _104908 f g p1 p2) = (term175 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375619) (@lem4375618 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375621 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term176 _104907 _104908 f g p1 p2) = (term177 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375620 _104907 _104908 f g p1 p2) (@lem4375615 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375622 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term91 _104907 _104908 f g p1 p2) = (term176 _104907 _104908 f g p1 p2).
Proof. exact (@lem17646 (term43 _104907 _104908 f p1 g p2) (term65 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375623 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term91 _104907 _104908 f g p1 p2) = (term177 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4375622 _104907 _104908 f g p1 p2) (@lem4375621 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375882 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4375883 {_104907 : Type'} (P : Prop) (Q : type686 _104907) : (term110 _104907 P Q) = (term111 _104907 P Q).
Proof. exact (@lem4375882 (_104907 -> Prop) P Q). Qed.
Lemma lem4375884 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term178 _104907 _104908 f g p1 p2) = (term179 _104907 _104908 f g p1 p2).
Proof. exact (@lem4375883 _104907 (term135 _104907 _104908 f p1 g p2) (term162 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375885 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term180 _104907 _104908 f g p1 p2 s) = (term154 _104907 _104908 f g s p1 p2).
Proof. exact (eq_refl (term180 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4375886 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term181 _104907 _104908 f g p1 p2) = (term162 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375885 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375887 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375888 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term182 _104907 _104908 f g p1 p2) = (term163 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375887 _104907) (@lem4375886 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375889 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term171 _104907 _104908 f p1 g p2) = (term171 _104907 _104908 f p1 g p2).
Proof. exact (eq_refl (term171 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375890 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term178 _104907 _104908 f g p1 p2) = (term173 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375889 _104907 _104908 f p1 g p2) (@lem4375888 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375892 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term183 _104907 _104908 f g p1 p2) = (term184 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375891) (@lem4375890 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375893 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term180 _104907 _104908 f g p1 p2 s) = (term154 _104907 _104908 f g s p1 p2).
Proof. exact (eq_refl (term180 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4375894 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term171 _104907 _104908 f p1 g p2) = (term171 _104907 _104908 f p1 g p2).
Proof. exact (eq_refl (term171 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375895 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term185 _104907 _104908 f g p1 p2 s) = (term186 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375894 _104907 _104908 f p1 g p2) (@lem4375893 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375896 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term187 _104907 _104908 f g p1 p2) = (term188 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375895 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375897 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375898 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term179 _104907 _104908 f g p1 p2) = (term189 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375897 _104907) (@lem4375896 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375899 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term178 _104907 _104908 f g p1 p2) = (term179 _104907 _104908 f g p1 p2)) = ((term173 _104907 _104908 f g p1 p2) = (term189 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4375892 _104907 _104908 f g p1 p2) (@lem4375898 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375900 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term173 _104907 _104908 f g p1 p2) = (term189 _104907 _104908 f g p1 p2).
Proof. exact (EQ_MP (@lem4375899 _104907 _104908 f g p1 p2) (@lem4375884 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375902 {A : Type'} (P : Prop) (Q : A -> Prop) : (term108 A P Q) = (term109 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4375903 {_104908 : Type'} (P : Prop) (Q : type686 _104908) : (term110 _104908 P Q) = (term111 _104908 P Q).
Proof. exact (@lem4375902 (_104908 -> Prop) P Q). Qed.
Lemma lem4375904 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term190 _104907 _104908 f g s p1 p2) = (term191 _104907 _104908 f g s p1 p2).
Proof. exact (@lem4375903 _104908 (term135 _104907 _104908 f p1 g p2) (term153 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375905 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term192 _104907 _104908 f g s p1 p2 t) = (term142 _104907 _104908 f g s p1 t p2).
Proof. exact (eq_refl (term192 _104907 _104908 f g s p1 p2 t)). Qed.
Lemma lem4375906 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term193 _104907 _104908 f g s p1 p2) = (term153 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375905 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375907 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375908 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term194 _104907 _104908 f g s p1 p2) = (term154 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375907 _104908) (@lem4375906 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375909 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term171 _104907 _104908 f p1 g p2) = (term171 _104907 _104908 f p1 g p2).
Proof. exact (eq_refl (term171 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375910 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term190 _104907 _104908 f g s p1 p2) = (term186 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375909 _104907 _104908 f p1 g p2) (@lem4375908 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375912 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term195 _104907 _104908 f g s p1 p2) = (term196 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375911) (@lem4375910 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375913 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term192 _104907 _104908 f g s p1 p2 t) = (term142 _104907 _104908 f g s p1 t p2).
Proof. exact (eq_refl (term192 _104907 _104908 f g s p1 p2 t)). Qed.
Lemma lem4375914 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term171 _104907 _104908 f p1 g p2) = (term171 _104907 _104908 f p1 g p2).
Proof. exact (eq_refl (term171 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375915 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term197 _104907 _104908 f g s p1 p2 t) = (term198 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4375914 _104907 _104908 f p1 g p2) (@lem4375913 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375916 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term199 _104907 _104908 f g s p1 p2) = (term200 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375915 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4375917 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375918 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term191 _104907 _104908 f g s p1 p2) = (term201 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4375917 _104908) (@lem4375916 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375919 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : ((term190 _104907 _104908 f g s p1 p2) = (term191 _104907 _104908 f g s p1 p2)) = ((term186 _104907 _104908 f g s p1 p2) = (term201 _104907 _104908 f g s p1 p2)).
Proof. exact (MK_COMB (@lem4375912 _104907 _104908 f g s p1 p2) (@lem4375918 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375920 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term186 _104907 _104908 f g s p1 p2) = (term201 _104907 _104908 f g s p1 p2).
Proof. exact (EQ_MP (@lem4375919 _104907 _104908 f g s p1 p2) (@lem4375904 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375921 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term188 _104907 _104908 f g p1 p2) = (term202 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4375920 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4375922 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375923 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term189 _104907 _104908 f g p1 p2) = (term203 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375922 _104907) (@lem4375921 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375924 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term173 _104907 _104908 f g p1 p2) = (term203 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4375900 _104907 _104908 f g p1 p2) (@lem4375923 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375925 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4375926 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term175 _104907 _104908 f g p1 p2) = (term204 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375925) (@lem4375924 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375930 {A : Type'} (P : A -> Prop) (Q : Prop) : (term205 A P Q) = (term206 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4375931 {_104907 : Type'} (P : type686 _104907) (Q : Prop) : (term207 _104907 P Q) = (term208 _104907 P Q).
Proof. exact (@lem4375930 (_104907 -> Prop) P Q). Qed.
Lemma lem4375932 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term209 _104907 _104908 f p1 g p2) = (term210 _104907 _104908 f p1 g p2).
Proof. exact (@lem4375931 _104907 (term125 _104907 f p1) (term126 _104908 g p2)). Qed.
Lemma lem4375933 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term211 _104907 f p1 t) = (term118 _104907 f t p1).
Proof. exact (eq_refl (term211 _104907 f p1 t)). Qed.
Lemma lem4375934 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term212 _104907 f p1) = (term125 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375933 _104907 f t p1)). Qed.
Lemma lem4375935 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375936 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term213 _104907 f p1) = (term126 _104907 f p1).
Proof. exact (MK_COMB (@lem4375935 _104907) (@lem4375934 _104907 f p1)). Qed.
Lemma lem4375937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4375938 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term214 _104907 f p1) = (term130 _104907 f p1).
Proof. exact (MK_COMB (@lem4375937) (@lem4375936 _104907 f p1)). Qed.
Lemma lem4375939 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term126 _104908 g p2) = (term126 _104908 g p2).
Proof. exact (eq_refl (term126 _104908 g p2)). Qed.
Lemma lem4375940 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term209 _104907 _104908 f p1 g p2) = (term132 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375938 _104907 f p1) (@lem4375939 _104908 g p2)). Qed.
Lemma lem4375941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375942 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term215 _104907 _104908 f p1 g p2) = (term216 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375941) (@lem4375940 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375943 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term211 _104907 f p1 t) = (term118 _104907 f t p1).
Proof. exact (eq_refl (term211 _104907 f p1 t)). Qed.
Lemma lem4375944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4375945 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term217 _104907 f p1 t) = (term218 _104907 f t p1).
Proof. exact (MK_COMB (@lem4375944) (@lem4375943 _104907 f t p1)). Qed.
Lemma lem4375946 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term126 _104908 g p2) = (term126 _104908 g p2).
Proof. exact (eq_refl (term126 _104908 g p2)). Qed.
Lemma lem4375947 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term219 _104907 _104908 f p1 t g p2) = (term220 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4375945 _104907 f t p1) (@lem4375946 _104908 g p2)). Qed.
Lemma lem4375948 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term221 _104907 _104908 f p1 g p2) = (term222 _104907 _104908 f p1 g p2).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375947 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375949 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375950 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term210 _104907 _104908 f p1 g p2) = (term223 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375949 _104907) (@lem4375948 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375951 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : ((term209 _104907 _104908 f p1 g p2) = (term210 _104907 _104908 f p1 g p2)) = ((term132 _104907 _104908 f p1 g p2) = (term223 _104907 _104908 f p1 g p2)).
Proof. exact (MK_COMB (@lem4375942 _104907 _104908 f p1 g p2) (@lem4375950 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375952 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term132 _104907 _104908 f p1 g p2) = (term223 _104907 _104908 f p1 g p2).
Proof. exact (EQ_MP (@lem4375951 _104907 _104908 f p1 g p2) (@lem4375932 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375954 {A : Type'} (P : Prop) (Q : A -> Prop) : (term224 A P Q) = (term225 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4375955 {_104908 : Type'} (P : Prop) (Q : type686 _104908) : (term226 _104908 P Q) = (term227 _104908 P Q).
Proof. exact (@lem4375954 (_104908 -> Prop) P Q). Qed.
Lemma lem4375956 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term228 _104907 _104908 f t p1 g p2) = (term229 _104907 _104908 f t p1 g p2).
Proof. exact (@lem4375955 _104908 (term118 _104907 f t p1) (term125 _104908 g p2)). Qed.
Lemma lem4375957 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term211 _104908 g p2 t) = (term118 _104908 g t p2).
Proof. exact (eq_refl (term211 _104908 g p2 t)). Qed.
Lemma lem4375958 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term212 _104908 g p2) = (term125 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4375957 _104908 g t p2)). Qed.
Lemma lem4375959 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375960 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term213 _104908 g p2) = (term126 _104908 g p2).
Proof. exact (MK_COMB (@lem4375959 _104908) (@lem4375958 _104908 g p2)). Qed.
Lemma lem4375961 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term218 _104907 f t p1) = (term218 _104907 f t p1).
Proof. exact (eq_refl (term218 _104907 f t p1)). Qed.
Lemma lem4375962 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term228 _104907 _104908 f t p1 g p2) = (term220 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4375961 _104907 f t p1) (@lem4375960 _104908 g p2)). Qed.
Lemma lem4375963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375964 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term230 _104907 _104908 f t p1 g p2) = (term231 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4375963) (@lem4375962 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375965 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term211 _104908 g p2 t) = (term118 _104908 g t p2).
Proof. exact (eq_refl (term211 _104908 g p2 t)). Qed.
Lemma lem4375966 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term218 _104907 f t p1) = (term218 _104907 f t p1).
Proof. exact (eq_refl (term218 _104907 f t p1)). Qed.
Lemma lem4375967 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (t' : _104908 -> Prop) (p2 : _104908) : (term232 _104907 _104908 f t p1 g p2 t') = (term233 _104907 _104908 f t p1 g t' p2).
Proof. exact (MK_COMB (@lem4375966 _104907 f t p1) (@lem4375965 _104908 g t' p2)). Qed.
Lemma lem4375968 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term234 _104907 _104908 f t p1 g p2) = (term235 _104907 _104908 f t p1 g p2).
Proof. exact (fun_ext (fun t' : _104908 -> Prop => @lem4375967 _104907 _104908 f t p1 g t' p2)). Qed.
Lemma lem4375969 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4375970 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term229 _104907 _104908 f t p1 g p2) = (term236 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4375969 _104908) (@lem4375968 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375971 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : ((term228 _104907 _104908 f t p1 g p2) = (term229 _104907 _104908 f t p1 g p2)) = ((term220 _104907 _104908 f t p1 g p2) = (term236 _104907 _104908 f t p1 g p2)).
Proof. exact (MK_COMB (@lem4375964 _104907 _104908 f t p1 g p2) (@lem4375970 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375972 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term220 _104907 _104908 f t p1 g p2) = (term236 _104907 _104908 f t p1 g p2).
Proof. exact (EQ_MP (@lem4375971 _104907 _104908 f t p1 g p2) (@lem4375956 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375973 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term222 _104907 _104908 f p1 g p2) = (term237 _104907 _104908 f p1 g p2).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375972 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375974 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375975 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term223 _104907 _104908 f p1 g p2) = (term238 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375974 _104907) (@lem4375973 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375976 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term132 _104907 _104908 f p1 g p2) = (term238 _104907 _104908 f p1 g p2).
Proof. exact (TRANS (@lem4375952 _104907 _104908 f p1 g p2) (@lem4375975 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375977 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375978 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term167 _104907 _104908 f p1 g p2) = (term239 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375977) (@lem4375976 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375979 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term165 _104907 _104908 f g p1 p2) = (term165 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375980 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term169 _104907 _104908 f g p1 p2) = (term240 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375978 _104907 _104908 f p1 g p2) (@lem4375979 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375982 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4375983 {_104907 : Type'} (P : type686 _104907) (Q : Prop) : (term105 _104907 P Q) = (term106 _104907 P Q).
Proof. exact (@lem4375982 (_104907 -> Prop) P Q). Qed.
Lemma lem4375984 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term241 _104907 _104908 f g p1 p2) = (term242 _104907 _104908 f g p1 p2).
Proof. exact (@lem4375983 _104907 (term237 _104907 _104908 f p1 g p2) (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375985 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term243 _104907 _104908 f p1 g p2 t) = (term236 _104907 _104908 f t p1 g p2).
Proof. exact (eq_refl (term243 _104907 _104908 f p1 g p2 t)). Qed.
Lemma lem4375986 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term244 _104907 _104908 f p1 g p2) = (term237 _104907 _104908 f p1 g p2).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375985 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375987 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4375988 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term245 _104907 _104908 f p1 g p2) = (term238 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375987 _104907) (@lem4375986 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375989 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375990 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term246 _104907 _104908 f p1 g p2) = (term239 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4375989) (@lem4375988 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4375991 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term165 _104907 _104908 f g p1 p2) = (term165 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375992 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term241 _104907 _104908 f g p1 p2) = (term240 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375990 _104907 _104908 f p1 g p2) (@lem4375991 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375993 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4375994 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term247 _104907 _104908 f g p1 p2) = (term248 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375993) (@lem4375992 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375995 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term243 _104907 _104908 f p1 g p2 t) = (term236 _104907 _104908 f t p1 g p2).
Proof. exact (eq_refl (term243 _104907 _104908 f p1 g p2 t)). Qed.
Lemma lem4375996 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4375997 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term249 _104907 _104908 f p1 g p2 t) = (term250 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4375996) (@lem4375995 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4375998 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term165 _104907 _104908 f g p1 p2) = (term165 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4375999 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term251 _104907 _104908 t f g p1 p2) = (term252 _104907 _104908 t f g p1 p2).
Proof. exact (MK_COMB (@lem4375997 _104907 _104908 f t p1 g p2) (@lem4375998 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376000 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term253 _104907 _104908 f g p1 p2) = (term254 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4375999 _104907 _104908 t f g p1 p2)). Qed.
Lemma lem4376001 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4376002 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term242 _104907 _104908 f g p1 p2) = (term255 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376001 _104907) (@lem4376000 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376003 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term241 _104907 _104908 f g p1 p2) = (term242 _104907 _104908 f g p1 p2)) = ((term240 _104907 _104908 f g p1 p2) = (term255 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4375994 _104907 _104908 f g p1 p2) (@lem4376002 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376004 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term240 _104907 _104908 f g p1 p2) = (term255 _104907 _104908 f g p1 p2).
Proof. exact (EQ_MP (@lem4376003 _104907 _104908 f g p1 p2) (@lem4375984 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376006 {A : Type'} (P : A -> Prop) (Q : Prop) : (term103 A P Q) = (term104 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4376007 {_104908 : Type'} (P : type686 _104908) (Q : Prop) : (term105 _104908 P Q) = (term106 _104908 P Q).
Proof. exact (@lem4376006 (_104908 -> Prop) P Q). Qed.
Lemma lem4376008 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term256 _104907 _104908 t f g p1 p2) = (term257 _104907 _104908 t f g p1 p2).
Proof. exact (@lem4376007 _104908 (term235 _104907 _104908 f t p1 g p2) (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376009 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (t' : _104908 -> Prop) (p2 : _104908) : (term258 _104907 _104908 f t p1 g p2 t') = (term233 _104907 _104908 f t p1 g t' p2).
Proof. exact (eq_refl (term258 _104907 _104908 f t p1 g p2 t')). Qed.
Lemma lem4376010 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term259 _104907 _104908 f t p1 g p2) = (term235 _104907 _104908 f t p1 g p2).
Proof. exact (fun_ext (fun t' : _104908 -> Prop => @lem4376009 _104907 _104908 f t p1 g t' p2)). Qed.
Lemma lem4376011 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4376012 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term260 _104907 _104908 f t p1 g p2) = (term236 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4376011 _104908) (@lem4376010 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4376013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376014 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term261 _104907 _104908 f t p1 g p2) = (term250 _104907 _104908 f t p1 g p2).
Proof. exact (MK_COMB (@lem4376013) (@lem4376012 _104907 _104908 f t p1 g p2)). Qed.
Lemma lem4376015 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term165 _104907 _104908 f g p1 p2) = (term165 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376016 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term256 _104907 _104908 t f g p1 p2) = (term252 _104907 _104908 t f g p1 p2).
Proof. exact (MK_COMB (@lem4376014 _104907 _104908 f t p1 g p2) (@lem4376015 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376017 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376018 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term262 _104907 _104908 t f g p1 p2) = (term263 _104907 _104908 t f g p1 p2).
Proof. exact (MK_COMB (@lem4376017) (@lem4376016 _104907 _104908 t f g p1 p2)). Qed.
Lemma lem4376019 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (t' : _104908 -> Prop) (p2 : _104908) : (term258 _104907 _104908 f t p1 g p2 t') = (term233 _104907 _104908 f t p1 g t' p2).
Proof. exact (eq_refl (term258 _104907 _104908 f t p1 g p2 t')). Qed.
Lemma lem4376020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376021 {_104907 _104908 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (t' : _104908 -> Prop) (p2 : _104908) : (term264 _104907 _104908 f t p1 g p2 t') = (term265 _104907 _104908 f t p1 g t' p2).
Proof. exact (MK_COMB (@lem4376020) (@lem4376019 _104907 _104908 f t p1 g t' p2)). Qed.
Lemma lem4376022 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term165 _104907 _104908 f g p1 p2) = (term165 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376023 {_104907 _104908 : Type'} (t : _104907 -> Prop) (t' : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term266 _104907 _104908 t t' f g p1 p2) = (term267 _104907 _104908 t t' f g p1 p2).
Proof. exact (MK_COMB (@lem4376021 _104907 _104908 f t p1 g t' p2) (@lem4376022 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376024 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term268 _104907 _104908 t f g p1 p2) = (term269 _104907 _104908 t f g p1 p2).
Proof. exact (fun_ext (fun t' : _104908 -> Prop => @lem4376023 _104907 _104908 t t' f g p1 p2)). Qed.
Lemma lem4376025 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4376026 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term257 _104907 _104908 t f g p1 p2) = (term270 _104907 _104908 t f g p1 p2).
Proof. exact (MK_COMB (@lem4376025 _104908) (@lem4376024 _104907 _104908 t f g p1 p2)). Qed.
Lemma lem4376027 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term256 _104907 _104908 t f g p1 p2) = (term257 _104907 _104908 t f g p1 p2)) = ((term252 _104907 _104908 t f g p1 p2) = (term270 _104907 _104908 t f g p1 p2)).
Proof. exact (MK_COMB (@lem4376018 _104907 _104908 t f g p1 p2) (@lem4376026 _104907 _104908 t f g p1 p2)). Qed.
Lemma lem4376028 {_104907 _104908 : Type'} (t : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term252 _104907 _104908 t f g p1 p2) = (term270 _104907 _104908 t f g p1 p2).
Proof. exact (EQ_MP (@lem4376027 _104907 _104908 t f g p1 p2) (@lem4376008 _104907 _104908 t f g p1 p2)). Qed.
Lemma lem4376029 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term254 _104907 _104908 f g p1 p2) = (term271 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4376028 _104907 _104908 t f g p1 p2)). Qed.
Lemma lem4376030 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4376031 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term255 _104907 _104908 f g p1 p2) = (term272 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376030 _104907) (@lem4376029 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376032 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term240 _104907 _104908 f g p1 p2) = (term272 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4376004 _104907 _104908 f g p1 p2) (@lem4376031 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376033 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term169 _104907 _104908 f g p1 p2) = (term272 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4375980 _104907 _104908 f g p1 p2) (@lem4376032 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376034 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term177 _104907 _104908 f g p1 p2) = (term273 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4375926 _104907 _104908 f g p1 p2) (@lem4376033 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376036 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4376037 {_104907 : Type'} (P : type686 _104907) (Q : type686 _104907) : (term276 _104907 P Q) = (term277 _104907 P Q).
Proof. exact (@lem4376036 (_104907 -> Prop) P Q). Qed.
Lemma lem4376038 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term278 _104907 _104908 f g p1 p2) = (term279 _104907 _104908 f g p1 p2).
Proof. exact (@lem4376037 _104907 (term202 _104907 _104908 f g p1 p2) (term271 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376039 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term280 _104907 _104908 f g p1 p2 s) = (term201 _104907 _104908 f g s p1 p2).
Proof. exact (eq_refl (term280 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4376040 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term281 _104907 _104908 f g p1 p2) = (term202 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376039 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4376041 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4376042 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term282 _104907 _104908 f g p1 p2) = (term203 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376041 _104907) (@lem4376040 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376043 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376044 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term283 _104907 _104908 f g p1 p2) = (term204 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376043) (@lem4376042 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376045 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term284 _104907 _104908 f g p1 p2 s) = (term270 _104907 _104908 s f g p1 p2).
Proof. exact (eq_refl (term284 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4376046 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term285 _104907 _104908 f g p1 p2) = (term271 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376045 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376047 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4376048 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term286 _104907 _104908 f g p1 p2) = (term272 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376047 _104907) (@lem4376046 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376049 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term278 _104907 _104908 f g p1 p2) = (term273 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376044 _104907 _104908 f g p1 p2) (@lem4376048 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376050 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376051 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term287 _104907 _104908 f g p1 p2) = (term288 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376050) (@lem4376049 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376052 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term280 _104907 _104908 f g p1 p2 s) = (term201 _104907 _104908 f g s p1 p2).
Proof. exact (eq_refl (term280 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4376053 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376054 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term289 _104907 _104908 f g p1 p2 s) = (term290 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4376053) (@lem4376052 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4376055 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term284 _104907 _104908 f g p1 p2 s) = (term270 _104907 _104908 s f g p1 p2).
Proof. exact (eq_refl (term284 _104907 _104908 f g p1 p2 s)). Qed.
Lemma lem4376056 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term291 _104907 _104908 f g p1 p2 s) = (term292 _104907 _104908 s f g p1 p2).
Proof. exact (MK_COMB (@lem4376054 _104907 _104908 f g s p1 p2) (@lem4376055 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376057 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term293 _104907 _104908 f g p1 p2) = (term294 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376056 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376058 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4376059 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term279 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376058 _104907) (@lem4376057 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376060 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term278 _104907 _104908 f g p1 p2) = (term279 _104907 _104908 f g p1 p2)) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)).
Proof. exact (MK_COMB (@lem4376051 _104907 _104908 f g p1 p2) (@lem4376059 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376061 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2).
Proof. exact (EQ_MP (@lem4376060 _104907 _104908 f g p1 p2) (@lem4376038 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376064 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term296 _104907 _104908 f g p1 p2) = (term296 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term296 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376065 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term296 _104907 _104908 f g p1 p2) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)).
Proof. exact (eq_refl (term296 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376066 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term297 _104907 _104908 f g p1 p2) = (term297 _104907 _104908 f g p1 p2).
Proof. exact (eq_refl (term297 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376067 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term296 _104907 _104908 f g p1 p2) = (term296 _104907 _104908 f g p1 p2)) = ((term296 _104907 _104908 f g p1 p2) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2))).
Proof. exact (MK_COMB (@lem4376066 _104907 _104908 f g p1 p2) (@lem4376065 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376068 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term296 _104907 _104908 f g p1 p2) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)).
Proof. exact (eq_refl (term296 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376069 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376070 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term297 _104907 _104908 f g p1 p2) = (term298 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376069) (@lem4376068 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376071 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)).
Proof. exact (eq_refl ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2))). Qed.
Lemma lem4376072 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term296 _104907 _104908 f g p1 p2) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2))) = (((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2))).
Proof. exact (MK_COMB (@lem4376070 _104907 _104908 f g p1 p2) (@lem4376071 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376073 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term296 _104907 _104908 f g p1 p2) = (term296 _104907 _104908 f g p1 p2)) = (((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2))).
Proof. exact (TRANS (@lem4376067 _104907 _104908 f g p1 p2) (@lem4376072 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376074 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)) = ((term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2)).
Proof. exact (EQ_MP (@lem4376073 _104907 _104908 f g p1 p2) (@lem4376064 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376075 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term273 _104907 _104908 f g p1 p2) = (term295 _104907 _104908 f g p1 p2).
Proof. exact (EQ_MP (@lem4376074 _104907 _104908 f g p1 p2) (@lem4376061 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376077 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term274 A P Q) = (term275 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4376078 {_104908 : Type'} (P : type686 _104908) (Q : type686 _104908) : (term276 _104908 P Q) = (term277 _104908 P Q).
Proof. exact (@lem4376077 (_104908 -> Prop) P Q). Qed.
Lemma lem4376079 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term299 _104907 _104908 s f g p1 p2) = (term300 _104907 _104908 s f g p1 p2).
Proof. exact (@lem4376078 _104908 (term200 _104907 _104908 f g s p1 p2) (term269 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376080 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term301 _104907 _104908 f g s p1 p2 t) = (term198 _104907 _104908 f g s p1 t p2).
Proof. exact (eq_refl (term301 _104907 _104908 f g s p1 p2 t)). Qed.
Lemma lem4376081 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term302 _104907 _104908 f g s p1 p2) = (term200 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376080 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4376082 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4376083 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term303 _104907 _104908 f g s p1 p2) = (term201 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4376082 _104908) (@lem4376081 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4376084 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376085 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term304 _104907 _104908 f g s p1 p2) = (term290 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4376084) (@lem4376083 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4376086 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term305 _104907 _104908 s f g p1 p2 t) = (term267 _104907 _104908 s t f g p1 p2).
Proof. exact (eq_refl (term305 _104907 _104908 s f g p1 p2 t)). Qed.
Lemma lem4376087 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term306 _104907 _104908 s f g p1 p2) = (term269 _104907 _104908 s f g p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376086 _104907 _104908 s t f g p1 p2)). Qed.
Lemma lem4376088 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4376089 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term307 _104907 _104908 s f g p1 p2) = (term270 _104907 _104908 s f g p1 p2).
Proof. exact (MK_COMB (@lem4376088 _104908) (@lem4376087 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376090 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term299 _104907 _104908 s f g p1 p2) = (term292 _104907 _104908 s f g p1 p2).
Proof. exact (MK_COMB (@lem4376085 _104907 _104908 f g s p1 p2) (@lem4376089 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376092 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term308 _104907 _104908 s f g p1 p2) = (term309 _104907 _104908 s f g p1 p2).
Proof. exact (MK_COMB (@lem4376091) (@lem4376090 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376093 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term301 _104907 _104908 f g s p1 p2 t) = (term198 _104907 _104908 f g s p1 t p2).
Proof. exact (eq_refl (term301 _104907 _104908 f g s p1 p2 t)). Qed.
Lemma lem4376094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376095 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term310 _104907 _104908 f g s p1 p2 t) = (term311 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4376094) (@lem4376093 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4376096 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term305 _104907 _104908 s f g p1 p2 t) = (term267 _104907 _104908 s t f g p1 p2).
Proof. exact (eq_refl (term305 _104907 _104908 s f g p1 p2 t)). Qed.
Lemma lem4376097 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term312 _104907 _104908 s f g p1 p2 t) = (term313 _104907 _104908 s t f g p1 p2).
Proof. exact (MK_COMB (@lem4376095 _104907 _104908 f g s p1 t p2) (@lem4376096 _104907 _104908 s t f g p1 p2)). Qed.
Lemma lem4376098 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term314 _104907 _104908 s f g p1 p2) = (term315 _104907 _104908 s f g p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376097 _104907 _104908 s t f g p1 p2)). Qed.
Lemma lem4376099 {_104908 : Type'} : (@ex (_104908 -> Prop)) = (@ex (_104908 -> Prop)).
Proof. exact (eq_refl (@ex (_104908 -> Prop))). Qed.
Lemma lem4376100 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term300 _104907 _104908 s f g p1 p2) = (term316 _104907 _104908 s f g p1 p2).
Proof. exact (MK_COMB (@lem4376099 _104908) (@lem4376098 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376101 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : ((term299 _104907 _104908 s f g p1 p2) = (term300 _104907 _104908 s f g p1 p2)) = ((term292 _104907 _104908 s f g p1 p2) = (term316 _104907 _104908 s f g p1 p2)).
Proof. exact (MK_COMB (@lem4376092 _104907 _104908 s f g p1 p2) (@lem4376100 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376102 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term292 _104907 _104908 s f g p1 p2) = (term316 _104907 _104908 s f g p1 p2).
Proof. exact (EQ_MP (@lem4376101 _104907 _104908 s f g p1 p2) (@lem4376079 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376103 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term294 _104907 _104908 f g p1 p2) = (term317 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376102 _104907 _104908 s f g p1 p2)). Qed.
Lemma lem4376104 {_104907 : Type'} : (@ex (_104907 -> Prop)) = (@ex (_104907 -> Prop)).
Proof. exact (eq_refl (@ex (_104907 -> Prop))). Qed.
Lemma lem4376105 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term295 _104907 _104908 f g p1 p2) = (term318 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376104 _104907) (@lem4376103 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376106 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term273 _104907 _104908 f g p1 p2) = (term318 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4376075 _104907 _104908 f g p1 p2) (@lem4376105 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376108 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term177 _104907 _104908 f g p1 p2) = (term318 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4376034 _104907 _104908 f g p1 p2) (@lem4376106 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376109 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term91 _104907 _104908 f g p1 p2) = (term318 _104907 _104908 f g p1 p2).
Proof. exact (TRANS (@lem4375623 _104907 _104908 f g p1 p2) (@lem4376108 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376110 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term91 _104907 _104908 f g p1 p2) : term318 _104907 _104908 f g p1 p2.
Proof. exact (EQ_MP (@lem4376109 _104907 _104908 f g p1 p2) (@lem4375437 _104907 _104908 f g p1 p2 h1)). Qed.
Lemma lem4376111 {_104907 _104908 : Type'} (s : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term316 _104907 _104908 s f g p1 p2) : term316 _104907 _104908 s f g p1 p2.
Proof. exact (h1). Qed.
Lemma lem4376112 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term313 _104907 _104908 s t f g p1 p2) : term313 _104907 _104908 s t f g p1 p2.
Proof. exact (h1). Qed.
Lemma lem4376113 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (h1 : term113 _104907 _104908 g x f) : term113 _104907 _104908 g x f.
Proof. exact (h1). Qed.
Lemma lem4376114 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : term319 _104907 _104908 g x f x'.
Proof. exact (h1). Qed.
Lemma lem4376119 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376120 {_104908 : Type'} (f : _104908 -> Prop) (x : _104908) : (f x) = (@I (_104908 -> Prop) f x).
Proof. exact (@lem4376119 _104908 Prop f x). Qed.
Lemma lem4376122 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (t p2) = (@I (_104908 -> Prop) t p2).
Proof. exact (@lem4376120 _104908 t p2). Qed.
Lemma lem4376127 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376128 {_104907 : Type'} (f : _104907 -> Prop) (x : _104907) : (f x) = (@I (_104907 -> Prop) f x).
Proof. exact (@lem4376127 _104907 Prop f x). Qed.
Lemma lem4376130 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (s p1) = (@I (_104907 -> Prop) s p1).
Proof. exact (@lem4376128 _104907 s p1). Qed.
Lemma lem4376131 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376132 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term53 _104907 s p1) = (term320 _104907 s p1).
Proof. exact (MK_COMB (@lem4376131) (@lem4376130 _104907 s p1)). Qed.
Lemma lem4376133 {_104907 _104908 : Type'} (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term55 _104907 _104908 s p1 t p2) = (term321 _104907 _104908 s p1 t p2).
Proof. exact (MK_COMB (@lem4376132 _104907 s p1) (@lem4376122 _104908 t p2)). Qed.
Lemma lem4376134 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376139 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376140 {_104908 : Type'} (f : type686 _104908) (x : _104908 -> Prop) : (f x) = (@I ((_104908 -> Prop) -> Prop) f x).
Proof. exact (@lem4376139 (_104908 -> Prop) Prop f x). Qed.
Lemma lem4376142 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (g t) = (@I ((_104908 -> Prop) -> Prop) g t).
Proof. exact (@lem4376140 _104908 g t). Qed.
Lemma lem4376143 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term23 _104908 g t) = (term322 _104908 g t).
Proof. exact (MK_COMB (@lem4376134) (@lem4376142 _104908 g t)). Qed.
Lemma lem4376144 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376149 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376150 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (f x) = (@I ((_104907 -> Prop) -> Prop) f x).
Proof. exact (@lem4376149 (_104907 -> Prop) Prop f x). Qed.
Lemma lem4376152 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (f s) = (@I ((_104907 -> Prop) -> Prop) f s).
Proof. exact (@lem4376150 _104907 f s). Qed.
Lemma lem4376153 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term23 _104907 f s) = (term322 _104907 f s).
Proof. exact (MK_COMB (@lem4376144) (@lem4376152 _104907 f s)). Qed.
Lemma lem4376154 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376155 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term323 _104907 f s) = (term324 _104907 f s).
Proof. exact (MK_COMB (@lem4376154) (@lem4376153 _104907 f s)). Qed.
Lemma lem4376156 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term137 _104907 _104908 f s g t) = (term325 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4376155 _104907 f s) (@lem4376143 _104908 g t)). Qed.
Lemma lem4376157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376158 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term145 _104907 _104908 f s g t) = (term326 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4376157) (@lem4376156 _104907 _104908 f s g t)). Qed.
Lemma lem4376159 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term147 _104907 _104908 f g s p1 t p2) = (term327 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4376158 _104907 _104908 f s g t) (@lem4376133 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4376160 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term155 _104907 _104908 f g s p1 p2) = (term328 _104907 _104908 f g s p1 p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376159 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4376161 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4376162 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) : (term156 _104907 _104908 f g s p1 p2) = (term329 _104907 _104908 f g s p1 p2).
Proof. exact (MK_COMB (@lem4376161 _104908) (@lem4376160 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4376163 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term164 _104907 _104908 f g p1 p2) = (term330 _104907 _104908 f g p1 p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376162 _104907 _104908 f g s p1 p2)). Qed.
Lemma lem4376164 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4376165 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term165 _104907 _104908 f g p1 p2) = (term331 _104907 _104908 f g p1 p2).
Proof. exact (MK_COMB (@lem4376164 _104907) (@lem4376163 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376166 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376171 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376172 {_104908 : Type'} (f : _104908 -> Prop) (x : _104908) : (f x) = (@I (_104908 -> Prop) f x).
Proof. exact (@lem4376171 _104908 Prop f x). Qed.
Lemma lem4376174 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (t p2) = (@I (_104908 -> Prop) t p2).
Proof. exact (@lem4376172 _104908 t p2). Qed.
Lemma lem4376175 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term332 _104908 t p2) = (term333 _104908 t p2).
Proof. exact (MK_COMB (@lem4376166) (@lem4376174 _104908 t p2)). Qed.
Lemma lem4376180 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376181 {_104908 : Type'} (f : type686 _104908) (x : _104908 -> Prop) : (f x) = (@I ((_104908 -> Prop) -> Prop) f x).
Proof. exact (@lem4376180 (_104908 -> Prop) Prop f x). Qed.
Lemma lem4376183 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (g t) = (@I ((_104908 -> Prop) -> Prop) g t).
Proof. exact (@lem4376181 _104908 g t). Qed.
Lemma lem4376184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376185 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term47 _104908 g t) = (term334 _104908 g t).
Proof. exact (MK_COMB (@lem4376184) (@lem4376183 _104908 g t)). Qed.
Lemma lem4376186 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term118 _104908 g t p2) = (term335 _104908 g t p2).
Proof. exact (MK_COMB (@lem4376185 _104908 g t) (@lem4376175 _104908 t p2)). Qed.
Lemma lem4376187 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376192 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376193 {_104907 : Type'} (f : _104907 -> Prop) (x : _104907) : (f x) = (@I (_104907 -> Prop) f x).
Proof. exact (@lem4376192 _104907 Prop f x). Qed.
Lemma lem4376195 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (s p1) = (@I (_104907 -> Prop) s p1).
Proof. exact (@lem4376193 _104907 s p1). Qed.
Lemma lem4376196 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term332 _104907 s p1) = (term333 _104907 s p1).
Proof. exact (MK_COMB (@lem4376187) (@lem4376195 _104907 s p1)). Qed.
Lemma lem4376201 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376202 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (f x) = (@I ((_104907 -> Prop) -> Prop) f x).
Proof. exact (@lem4376201 (_104907 -> Prop) Prop f x). Qed.
Lemma lem4376204 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (f s) = (@I ((_104907 -> Prop) -> Prop) f s).
Proof. exact (@lem4376202 _104907 f s). Qed.
Lemma lem4376205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376206 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term47 _104907 f s) = (term334 _104907 f s).
Proof. exact (MK_COMB (@lem4376205) (@lem4376204 _104907 f s)). Qed.
Lemma lem4376207 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) : (term118 _104907 f s p1) = (term335 _104907 f s p1).
Proof. exact (MK_COMB (@lem4376206 _104907 f s) (@lem4376196 _104907 s p1)). Qed.
Lemma lem4376208 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376209 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) : (term218 _104907 f s p1) = (term336 _104907 f s p1).
Proof. exact (MK_COMB (@lem4376208) (@lem4376207 _104907 f s p1)). Qed.
Lemma lem4376210 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term233 _104907 _104908 f s p1 g t p2) = (term337 _104907 _104908 f s p1 g t p2).
Proof. exact (MK_COMB (@lem4376209 _104907 f s p1) (@lem4376186 _104908 g t p2)). Qed.
Lemma lem4376211 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376212 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term265 _104907 _104908 f s p1 g t p2) = (term338 _104907 _104908 f s p1 g t p2).
Proof. exact (MK_COMB (@lem4376211) (@lem4376210 _104907 _104908 f s p1 g t p2)). Qed.
Lemma lem4376213 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term267 _104907 _104908 s t f g p1 p2) = (term339 _104907 _104908 s t f g p1 p2).
Proof. exact (MK_COMB (@lem4376212 _104907 _104908 f s p1 g t p2) (@lem4376165 _104907 _104908 f g p1 p2)). Qed.
Lemma lem4376214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376219 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376220 {_104908 : Type'} (f : _104908 -> Prop) (x : _104908) : (f x) = (@I (_104908 -> Prop) f x).
Proof. exact (@lem4376219 _104908 Prop f x). Qed.
Lemma lem4376222 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (t p2) = (@I (_104908 -> Prop) t p2).
Proof. exact (@lem4376220 _104908 t p2). Qed.
Lemma lem4376223 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term332 _104908 t p2) = (term333 _104908 t p2).
Proof. exact (MK_COMB (@lem4376214) (@lem4376222 _104908 t p2)). Qed.
Lemma lem4376224 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376229 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376230 {_104907 : Type'} (f : _104907 -> Prop) (x : _104907) : (f x) = (@I (_104907 -> Prop) f x).
Proof. exact (@lem4376229 _104907 Prop f x). Qed.
Lemma lem4376232 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (s p1) = (@I (_104907 -> Prop) s p1).
Proof. exact (@lem4376230 _104907 s p1). Qed.
Lemma lem4376233 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term332 _104907 s p1) = (term333 _104907 s p1).
Proof. exact (MK_COMB (@lem4376224) (@lem4376232 _104907 s p1)). Qed.
Lemma lem4376234 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376235 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term340 _104907 s p1) = (term341 _104907 s p1).
Proof. exact (MK_COMB (@lem4376234) (@lem4376233 _104907 s p1)). Qed.
Lemma lem4376236 {_104907 _104908 : Type'} (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term139 _104907 _104908 s p1 t p2) = (term342 _104907 _104908 s p1 t p2).
Proof. exact (MK_COMB (@lem4376235 _104907 s p1) (@lem4376223 _104908 t p2)). Qed.
Lemma lem4376241 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376242 {_104908 : Type'} (f : type686 _104908) (x : _104908 -> Prop) : (f x) = (@I ((_104908 -> Prop) -> Prop) f x).
Proof. exact (@lem4376241 (_104908 -> Prop) Prop f x). Qed.
Lemma lem4376244 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (g t) = (@I ((_104908 -> Prop) -> Prop) g t).
Proof. exact (@lem4376242 _104908 g t). Qed.
Lemma lem4376249 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376250 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (f x) = (@I ((_104907 -> Prop) -> Prop) f x).
Proof. exact (@lem4376249 (_104907 -> Prop) Prop f x). Qed.
Lemma lem4376252 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (f s) = (@I ((_104907 -> Prop) -> Prop) f s).
Proof. exact (@lem4376250 _104907 f s). Qed.
Lemma lem4376253 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376254 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term47 _104907 f s) = (term334 _104907 f s).
Proof. exact (MK_COMB (@lem4376253) (@lem4376252 _104907 f s)). Qed.
Lemma lem4376255 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term49 _104907 _104908 f s g t) = (term343 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4376254 _104907 f s) (@lem4376244 _104908 g t)). Qed.
Lemma lem4376256 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376257 {_104907 _104908 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) : (term140 _104907 _104908 f s g t) = (term344 _104907 _104908 f s g t).
Proof. exact (MK_COMB (@lem4376256) (@lem4376255 _104907 _104908 f s g t)). Qed.
Lemma lem4376258 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term142 _104907 _104908 f g s p1 t p2) = (term345 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4376257 _104907 _104908 f s g t) (@lem4376236 _104907 _104908 s p1 t p2)). Qed.
Lemma lem4376263 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376264 {_104908 : Type'} (f : _104908 -> Prop) (x : _104908) : (f x) = (@I (_104908 -> Prop) f x).
Proof. exact (@lem4376263 _104908 Prop f x). Qed.
Lemma lem4376266 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (t p2) = (@I (_104908 -> Prop) t p2).
Proof. exact (@lem4376264 _104908 t p2). Qed.
Lemma lem4376267 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376272 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376273 {_104908 : Type'} (f : type686 _104908) (x : _104908 -> Prop) : (f x) = (@I ((_104908 -> Prop) -> Prop) f x).
Proof. exact (@lem4376272 (_104908 -> Prop) Prop f x). Qed.
Lemma lem4376275 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (g t) = (@I ((_104908 -> Prop) -> Prop) g t).
Proof. exact (@lem4376273 _104908 g t). Qed.
Lemma lem4376276 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term23 _104908 g t) = (term322 _104908 g t).
Proof. exact (MK_COMB (@lem4376267) (@lem4376275 _104908 g t)). Qed.
Lemma lem4376277 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376278 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term323 _104908 g t) = (term324 _104908 g t).
Proof. exact (MK_COMB (@lem4376277) (@lem4376276 _104908 g t)). Qed.
Lemma lem4376279 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term119 _104908 g t p2) = (term346 _104908 g t p2).
Proof. exact (MK_COMB (@lem4376278 _104908 g t) (@lem4376266 _104908 t p2)). Qed.
Lemma lem4376280 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term127 _104908 g p2) = (term347 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376279 _104908 g t p2)). Qed.
Lemma lem4376281 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4376282 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term128 _104908 g p2) = (term348 _104908 g p2).
Proof. exact (MK_COMB (@lem4376281 _104908) (@lem4376280 _104908 g p2)). Qed.
Lemma lem4376287 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376288 {_104907 : Type'} (f : _104907 -> Prop) (x : _104907) : (f x) = (@I (_104907 -> Prop) f x).
Proof. exact (@lem4376287 _104907 Prop f x). Qed.
Lemma lem4376290 {_104907 : Type'} (t : _104907 -> Prop) (p1 : _104907) : (t p1) = (@I (_104907 -> Prop) t p1).
Proof. exact (@lem4376288 _104907 t p1). Qed.
Lemma lem4376291 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4376296 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376297 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (f x) = (@I ((_104907 -> Prop) -> Prop) f x).
Proof. exact (@lem4376296 (_104907 -> Prop) Prop f x). Qed.
Lemma lem4376299 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (f t) = (@I ((_104907 -> Prop) -> Prop) f t).
Proof. exact (@lem4376297 _104907 f t). Qed.
Lemma lem4376300 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (term23 _104907 f t) = (term322 _104907 f t).
Proof. exact (MK_COMB (@lem4376291) (@lem4376299 _104907 f t)). Qed.
Lemma lem4376301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376302 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) : (term323 _104907 f t) = (term324 _104907 f t).
Proof. exact (MK_COMB (@lem4376301) (@lem4376300 _104907 f t)). Qed.
Lemma lem4376303 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term119 _104907 f t p1) = (term346 _104907 f t p1).
Proof. exact (MK_COMB (@lem4376302 _104907 f t) (@lem4376290 _104907 t p1)). Qed.
Lemma lem4376304 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term127 _104907 f p1) = (term347 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4376303 _104907 f t p1)). Qed.
Lemma lem4376305 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4376306 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term128 _104907 f p1) = (term348 _104907 f p1).
Proof. exact (MK_COMB (@lem4376305 _104907) (@lem4376304 _104907 f p1)). Qed.
Lemma lem4376307 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376308 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term134 _104907 f p1) = (term349 _104907 f p1).
Proof. exact (MK_COMB (@lem4376307) (@lem4376306 _104907 f p1)). Qed.
Lemma lem4376309 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term135 _104907 _104908 f p1 g p2) = (term350 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4376308 _104907 f p1) (@lem4376282 _104908 g p2)). Qed.
Lemma lem4376310 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376311 {_104907 _104908 : Type'} (f : type686 _104907) (p1 : _104907) (g : type686 _104908) (p2 : _104908) : (term171 _104907 _104908 f p1 g p2) = (term351 _104907 _104908 f p1 g p2).
Proof. exact (MK_COMB (@lem4376310) (@lem4376309 _104907 _104908 f p1 g p2)). Qed.
Lemma lem4376312 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term198 _104907 _104908 f g s p1 t p2) = (term352 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4376311 _104907 _104908 f p1 g p2) (@lem4376258 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4376313 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4376314 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) : (term311 _104907 _104908 f g s p1 t p2) = (term353 _104907 _104908 f g s p1 t p2).
Proof. exact (MK_COMB (@lem4376313) (@lem4376312 _104907 _104908 f g s p1 t p2)). Qed.
Lemma lem4376315 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) : (term313 _104907 _104908 s t f g p1 p2) = (term354 _104907 _104908 s t f g p1 p2).
Proof. exact (MK_COMB (@lem4376314 _104907 _104908 f g s p1 t p2) (@lem4376213 _104907 _104908 s t f g p1 p2)). Qed.
Lemma lem4376316 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term313 _104907 _104908 s t f g p1 p2) : term354 _104907 _104908 s t f g p1 p2.
Proof. exact (EQ_MP (@lem4376315 _104907 _104908 s t f g p1 p2) (@lem4376112 _104907 _104908 s t f g p1 p2 h1)). Qed.
Lemma lem4376321 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376322 {_104907 : Type'} (f : type686 _104907) (x : _104907 -> Prop) : (f x) = (@I ((_104907 -> Prop) -> Prop) f x).
Proof. exact (@lem4376321 (_104907 -> Prop) Prop f x). Qed.
Lemma lem4376324 {_104907 : Type'} (f : type686 _104907) (x' : _104907 -> Prop) : (f x') = (@I ((_104907 -> Prop) -> Prop) f x').
Proof. exact (@lem4376322 _104907 f x'). Qed.
Lemma lem4376329 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem4376330 {_104908 : Type'} (f : type686 _104908) (x : _104908 -> Prop) : (f x) = (@I ((_104908 -> Prop) -> Prop) f x).
Proof. exact (@lem4376329 (_104908 -> Prop) Prop f x). Qed.
Lemma lem4376332 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (g x) = (@I ((_104908 -> Prop) -> Prop) g x).
Proof. exact (@lem4376330 _104908 g x). Qed.
Lemma lem4376333 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376334 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term47 _104908 g x) = (term334 _104908 g x).
Proof. exact (MK_COMB (@lem4376333) (@lem4376332 _104908 g x)). Qed.
Lemma lem4376335 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) : (term319 _104907 _104908 g x f x') = (term355 _104907 _104908 g x f x').
Proof. exact (MK_COMB (@lem4376334 _104908 g x) (@lem4376324 _104907 f x')). Qed.
Lemma lem4376336 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : term355 _104907 _104908 g x f x'.
Proof. exact (EQ_MP (@lem4376335 _104907 _104908 g x f x') (@lem4376114 _104907 _104908 g x f x' h1)). Qed.
Lemma lem4376339 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term352 _104907 _104908 f g s p1 t p2.
Proof. exact (h1). Qed.
Lemma lem4376340 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term339 _104907 _104908 s t f g p1 p2.
Proof. exact (h1). Qed.
Lemma lem4376341 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term345 _104907 _104908 f g s p1 t p2.
Proof. exact (proj2 (@lem4376339 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376342 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term350 _104907 _104908 f p1 g p2.
Proof. exact (proj1 (@lem4376339 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376343 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term342 _104907 _104908 s p1 t p2.
Proof. exact (proj2 (@lem4376341 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376344 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term343 _104907 _104908 f s g t.
Proof. exact (proj1 (@lem4376341 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376347 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term348 _104908 g p2.
Proof. exact (proj2 (@lem4376342 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376348 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term348 _104907 f p1.
Proof. exact (proj1 (@lem4376342 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376351 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term331 _104907 _104908 f g p1 p2.
Proof. exact (proj2 (@lem4376340 _104907 _104908 s t f g p1 p2 h1)). Qed.
Lemma lem4376352 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term337 _104907 _104908 f s p1 g t p2.
Proof. exact (proj1 (@lem4376340 _104907 _104908 s t f g p1 p2 h1)). Qed.
Lemma lem4376353 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term335 _104907 f s p1) : term335 _104907 f s p1.
Proof. exact (h1). Qed.
Lemma lem4376354 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term335 _104908 g t p2) : term335 _104908 g t p2.
Proof. exact (h1). Qed.
Lemma lem4376382 {_104907 : Type'} (f : type686 _104907) (t : _104907 -> Prop) (p1 : _104907) : (term346 _104907 f t p1) = (term346 _104907 f t p1).
Proof. exact (eq_refl (term346 _104907 f t p1)). Qed.
Lemma lem4376383 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term347 _104907 f p1) = (term347 _104907 f p1).
Proof. exact (fun_ext (fun t : _104907 -> Prop => @lem4376382 _104907 f t p1)). Qed.
Lemma lem4376384 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4376386 {_104907 : Type'} (f : type686 _104907) (p1 : _104907) : (term348 _104907 f p1) = (term348 _104907 f p1).
Proof. exact (MK_COMB (@lem4376384 _104907) (@lem4376383 _104907 f p1)). Qed.
Lemma lem4376387 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term348 _104907 f p1.
Proof. exact (EQ_MP (@lem4376386 _104907 f p1) (@lem4376348 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376404 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) (h1 : term333 _104907 s p1) : term333 _104907 s p1.
Proof. exact (h1). Qed.
Lemma lem4376441 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term346 _104908 g t p2) = (term346 _104908 g t p2).
Proof. exact (eq_refl (term346 _104908 g t p2)). Qed.
Lemma lem4376442 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term347 _104908 g p2) = (term347 _104908 g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376441 _104908 g t p2)). Qed.
Lemma lem4376443 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4376445 {_104908 : Type'} (g : type686 _104908) (p2 : _104908) : (term348 _104908 g p2) = (term348 _104908 g p2).
Proof. exact (MK_COMB (@lem4376443 _104908) (@lem4376442 _104908 g p2)). Qed.
Lemma lem4376446 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term348 _104908 g p2.
Proof. exact (EQ_MP (@lem4376445 _104908 g p2) (@lem4376347 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376450 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) : term333 _104908 t p2.
Proof. exact (h1). Qed.
Lemma lem4376482 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term327 _104907 _104908 f g s p1 t p2) = (term356 _104907 _104908 p1 f s g t p2).
Proof. exact (@lem19490 (@I (_104907 -> Prop) s p1) (term325 _104907 _104908 f s g t) (@I (_104908 -> Prop) t p2)). Qed.
Lemma lem4376483 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (p2 : _104908) : (term328 _104907 _104908 f g s p1 p2) = (term357 _104907 _104908 p1 f s g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376482 _104907 _104908 p1 f s g t p2)). Qed.
Lemma lem4376484 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4376485 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (p2 : _104908) : (term329 _104907 _104908 f g s p1 p2) = (term358 _104907 _104908 p1 f s g p2).
Proof. exact (MK_COMB (@lem4376484 _104908) (@lem4376483 _104907 _104908 p1 f s g p2)). Qed.
Lemma lem4376486 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (g : type686 _104908) (p2 : _104908) : (term330 _104907 _104908 f g p1 p2) = (term359 _104907 _104908 p1 f g p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376485 _104907 _104908 p1 f s g p2)). Qed.
Lemma lem4376487 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4376489 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (g : type686 _104908) (p2 : _104908) : (term331 _104907 _104908 f g p1 p2) = (term360 _104907 _104908 p1 f g p2).
Proof. exact (MK_COMB (@lem4376487 _104907) (@lem4376486 _104907 _104908 p1 f g p2)). Qed.
Lemma lem4376490 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term360 _104907 _104908 p1 f g p2.
Proof. exact (EQ_MP (@lem4376489 _104907 _104908 p1 f g p2) (@lem4376351 _104907 _104908 s t f g p1 p2 h1)). Qed.
Lemma lem4376530 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) : (term327 _104907 _104908 f g s p1 t p2) = (term356 _104907 _104908 p1 f s g t p2).
Proof. exact (@lem19490 (@I (_104907 -> Prop) s p1) (term325 _104907 _104908 f s g t) (@I (_104908 -> Prop) t p2)). Qed.
Lemma lem4376531 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (p2 : _104908) : (term328 _104907 _104908 f g s p1 p2) = (term357 _104907 _104908 p1 f s g p2).
Proof. exact (fun_ext (fun t : _104908 -> Prop => @lem4376530 _104907 _104908 p1 f s g t p2)). Qed.
Lemma lem4376532 {_104908 : Type'} : (@all (_104908 -> Prop)) = (@all (_104908 -> Prop)).
Proof. exact (eq_refl (@all (_104908 -> Prop))). Qed.
Lemma lem4376533 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (s : _104907 -> Prop) (g : type686 _104908) (p2 : _104908) : (term329 _104907 _104908 f g s p1 p2) = (term358 _104907 _104908 p1 f s g p2).
Proof. exact (MK_COMB (@lem4376532 _104908) (@lem4376531 _104907 _104908 p1 f s g p2)). Qed.
Lemma lem4376534 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (g : type686 _104908) (p2 : _104908) : (term330 _104907 _104908 f g p1 p2) = (term359 _104907 _104908 p1 f g p2).
Proof. exact (fun_ext (fun s : _104907 -> Prop => @lem4376533 _104907 _104908 p1 f s g p2)). Qed.
Lemma lem4376535 {_104907 : Type'} : (@all (_104907 -> Prop)) = (@all (_104907 -> Prop)).
Proof. exact (eq_refl (@all (_104907 -> Prop))). Qed.
Lemma lem4376537 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (g : type686 _104908) (p2 : _104908) : (term331 _104907 _104908 f g p1 p2) = (term360 _104907 _104908 p1 f g p2).
Proof. exact (MK_COMB (@lem4376535 _104907) (@lem4376534 _104907 _104908 p1 f g p2)). Qed.
Lemma lem4376538 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term360 _104907 _104908 p1 f g p2.
Proof. exact (EQ_MP (@lem4376537 _104907 _104908 p1 f g p2) (@lem4376351 _104907 _104908 s t f g p1 p2 h1)). Qed.
Lemma lem4376547 {_104907 _104908 : Type'} (_50028 : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term361 _104907 f p1 _50028.
Proof. exact (@lem4376387 _104907 _104908 f g s p1 t p2 h1 _50028). Qed.
Lemma lem4376548 {_104907 : Type'} (f : type686 _104907) (_50028 : _104907 -> Prop) (p1 : _104907) : (term361 _104907 f p1 _50028) = (term346 _104907 f _50028 p1).
Proof. exact (eq_refl (term361 _104907 f p1 _50028)). Qed.
Lemma lem4376556 {_104907 _104908 : Type'} (_50031 : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term361 _104908 g p2 _50031.
Proof. exact (@lem4376446 _104907 _104908 f g s p1 t p2 h1 _50031). Qed.
Lemma lem4376557 {_104908 : Type'} (g : type686 _104908) (_50031 : _104908 -> Prop) (p2 : _104908) : (term361 _104908 g p2 _50031) = (term346 _104908 g _50031 p2).
Proof. exact (eq_refl (term361 _104908 g p2 _50031)). Qed.
Lemma lem4376559 {_104907 _104908 : Type'} (_50032 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term362 _104907 _104908 p1 f g p2 _50032.
Proof. exact (@lem4376490 _104907 _104908 s t f g p1 p2 h1 _50032). Qed.
Lemma lem4376560 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (p2 : _104908) : (term362 _104907 _104908 p1 f g p2 _50032) = (term358 _104907 _104908 p1 f _50032 g p2).
Proof. exact (eq_refl (term362 _104907 _104908 p1 f g p2 _50032)). Qed.
Lemma lem4376561 {_104907 _104908 : Type'} (_50032 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term358 _104907 _104908 p1 f _50032 g p2.
Proof. exact (EQ_MP (@lem4376560 _104907 _104908 p1 f _50032 g p2) (@lem4376559 _104907 _104908 _50032 s t f g p1 p2 h1)). Qed.
Lemma lem4376562 {_104907 _104908 : Type'} (_50032 : _104907 -> Prop) (_50033 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term363 _104907 _104908 p1 f _50032 g p2 _50033.
Proof. exact (@lem4376561 _104907 _104908 _50032 s t f g p1 p2 h1 _50033). Qed.
Lemma lem4376563 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) (p2 : _104908) : (term363 _104907 _104908 p1 f _50032 g p2 _50033) = (term356 _104907 _104908 p1 f _50032 g _50033 p2).
Proof. exact (eq_refl (term363 _104907 _104908 p1 f _50032 g p2 _50033)). Qed.
Lemma lem4376564 {_104907 _104908 : Type'} (_50032 : _104907 -> Prop) (_50033 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term356 _104907 _104908 p1 f _50032 g _50033 p2.
Proof. exact (EQ_MP (@lem4376563 _104907 _104908 p1 f _50032 g _50033 p2) (@lem4376562 _104907 _104908 _50032 _50033 s t f g p1 p2 h1)). Qed.
Lemma lem4376565 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term362 _104907 _104908 p1 f g p2 _50034.
Proof. exact (@lem4376538 _104907 _104908 s t f g p1 p2 h1 _50034). Qed.
Lemma lem4376566 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (p2 : _104908) : (term362 _104907 _104908 p1 f g p2 _50034) = (term358 _104907 _104908 p1 f _50034 g p2).
Proof. exact (eq_refl (term362 _104907 _104908 p1 f g p2 _50034)). Qed.
Lemma lem4376567 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term358 _104907 _104908 p1 f _50034 g p2.
Proof. exact (EQ_MP (@lem4376566 _104907 _104908 p1 f _50034 g p2) (@lem4376565 _104907 _104908 _50034 s t f g p1 p2 h1)). Qed.
Lemma lem4376568 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term363 _104907 _104908 p1 f _50034 g p2 _50035.
Proof. exact (@lem4376567 _104907 _104908 _50034 s t f g p1 p2 h1 _50035). Qed.
Lemma lem4376569 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) (p2 : _104908) : (term363 _104907 _104908 p1 f _50034 g p2 _50035) = (term356 _104907 _104908 p1 f _50034 g _50035 p2).
Proof. exact (eq_refl (term363 _104907 _104908 p1 f _50034 g p2 _50035)). Qed.
Lemma lem4376570 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term356 _104907 _104908 p1 f _50034 g _50035 p2.
Proof. exact (EQ_MP (@lem4376569 _104907 _104908 p1 f _50034 g _50035 p2) (@lem4376568 _104907 _104908 _50034 _50035 s t f g p1 p2 h1)). Qed.
Lemma lem4376572 {_104907 _104908 : Type'} (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term364 _104907 _104908 f g _50033 _50032 p1.
Proof. exact (proj1 (@lem4376564 _104907 _104908 _50032 _50033 s t f g p1 p2 h1)). Qed.
Lemma lem4376573 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term365 _104907 _104908 f _50034 g _50035 p2.
Proof. exact (proj2 (@lem4376570 _104907 _104908 _50034 _50035 s t f g p1 p2 h1)). Qed.
Lemma lem4376588 {_104907 _104908 : Type'} (_50028 : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term346 _104907 f _50028 p1.
Proof. exact (EQ_MP (@lem4376548 _104907 f _50028 p1) (@lem4376547 _104907 _104908 _50028 f g s p1 t p2 h1)). Qed.
Lemma lem4376596 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) (h1 : term333 _104907 s p1) : term333 _104907 s p1.
Proof. exact (h1). Qed.
Lemma lem4376616 {_104907 _104908 : Type'} (_50031 : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term346 _104908 g _50031 p2.
Proof. exact (EQ_MP (@lem4376557 _104908 g _50031 p2) (@lem4376556 _104907 _104908 _50031 f g s p1 t p2 h1)). Qed.
Lemma lem4376618 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) : term333 _104908 t p2.
Proof. exact (h1). Qed.
Lemma lem4376626 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term335 _104907 f s p1) : term333 _104907 s p1.
Proof. exact (proj2 (@lem4376353 _104907 f s p1 h1)). Qed.
Lemma lem4376637 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (p1 : _104907) : (term364 _104907 _104908 f g _50033 _50032 p1) = (term366 _104907 _104908 f g _50033 _50032 p1).
Proof. exact (@lem4374867 (term322 _104907 f _50032) (term322 _104908 g _50033) (@I (_104907 -> Prop) _50032 p1)). Qed.
Lemma lem4376638 {_104907 _104908 : Type'} (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term366 _104907 _104908 f g _50033 _50032 p1.
Proof. exact (EQ_MP (@lem4376637 _104907 _104908 f g _50033 _50032 p1) (@lem4376572 _104907 _104908 _50033 _50032 s t f g p1 p2 h1)). Qed.
Lemma lem4376658 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term335 _104908 g t p2) : term333 _104908 t p2.
Proof. exact (proj2 (@lem4376354 _104908 g t p2 h1)). Qed.
Lemma lem4376681 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) (p2 : _104908) : (term365 _104907 _104908 f _50034 g _50035 p2) = (term367 _104907 _104908 f _50034 g _50035 p2).
Proof. exact (@lem4374867 (term322 _104907 f _50034) (term322 _104908 g _50035) (@I (_104908 -> Prop) _50035 p2)). Qed.
Lemma lem4376682 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term367 _104907 _104908 f _50034 g _50035 p2.
Proof. exact (EQ_MP (@lem4376681 _104907 _104908 f _50034 g _50035 p2) (@lem4376573 _104907 _104908 _50034 _50035 s t f g p1 p2 h1)). Qed.
Lemma lem4376684 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I ((_104907 -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem4376344 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376685 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term368 _104907 f s.
Proof. exact (fun h0 : term322 _104907 f s => @lem4376684 _104907 _104908 f g s p1 t p2 h1). Qed.
Lemma lem4376687 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376688 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term368 _104907 f s) = (@I ((_104907 -> Prop) -> Prop) f s).
Proof. exact (@lem4376687 (@I ((_104907 -> Prop) -> Prop) f s)). Qed.
Lemma lem4376689 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I ((_104907 -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem4376688 _104907 f s) (@lem4376685 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376695 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4376696 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : (term346 _104907 f _50028 p1) = (term370 _104907 p1 f _50028).
Proof. exact (@lem4376695 (@I (_104907 -> Prop) _50028 p1) (term322 _104907 f _50028)). Qed.
Lemma lem4376702 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376703 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : (term371 _104907 f _50028 p1) = (term372 _104907 p1 f _50028).
Proof. exact (MK_COMB (@lem4376702) (@lem4376696 _104907 p1 f _50028)). Qed.
Lemma lem4376709 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : (term370 _104907 p1 f _50028) = (term370 _104907 p1 f _50028).
Proof. exact (eq_refl (term370 _104907 p1 f _50028)). Qed.
Lemma lem4376710 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : ((term346 _104907 f _50028 p1) = (term370 _104907 p1 f _50028)) = ((term370 _104907 p1 f _50028) = (term370 _104907 p1 f _50028)).
Proof. exact (MK_COMB (@lem4376703 _104907 p1 f _50028) (@lem4376709 _104907 p1 f _50028)). Qed.
Lemma lem4376712 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4376713 (x : Prop) : (x = x) = True.
Proof. exact (@lem4376712 Prop x). Qed.
Lemma lem4376714 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : ((term370 _104907 p1 f _50028) = (term370 _104907 p1 f _50028)) = True.
Proof. exact (@lem4376713 (term370 _104907 p1 f _50028)). Qed.
Lemma lem4376715 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : ((term346 _104907 f _50028 p1) = (term370 _104907 p1 f _50028)) = True.
Proof. exact (TRANS (@lem4376710 _104907 p1 f _50028) (@lem4376714 _104907 p1 f _50028)). Qed.
Lemma lem4376716 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : True = ((term346 _104907 f _50028 p1) = (term370 _104907 p1 f _50028)).
Proof. exact (SYM (@lem4376715 _104907 p1 f _50028)). Qed.
Lemma lem4376717 {_104907 : Type'} (p1 : _104907) (f : type686 _104907) (_50028 : _104907 -> Prop) : (term346 _104907 f _50028 p1) = (term370 _104907 p1 f _50028).
Proof. exact (EQ_MP (@lem4376716 _104907 p1 f _50028) (@lem0)). Qed.
Lemma lem4376718 {_104907 _104908 : Type'} (_50028 : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term370 _104907 p1 f _50028.
Proof. exact (EQ_MP (@lem4376717 _104907 p1 f _50028) (@lem4376588 _104907 _104908 _50028 f g s p1 t p2 h1)). Qed.
Lemma lem4376720 (b : Prop) (a : Prop) : (a \/ b) = (term373 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4376721 {_104907 : Type'} (f : type686 _104907) (_50028 : _104907 -> Prop) (p1 : _104907) : (term370 _104907 p1 f _50028) = (term374 _104907 f _50028 p1).
Proof. exact (@lem4376720 (term322 _104907 f _50028) (@I (_104907 -> Prop) _50028 p1)). Qed.
Lemma lem4376723 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4376724 {_104907 : Type'} (f : type686 _104907) (_50028 : _104907 -> Prop) : (term375 _104907 f _50028) = (@I ((_104907 -> Prop) -> Prop) f _50028).
Proof. exact (@lem4376723 (@I ((_104907 -> Prop) -> Prop) f _50028)). Qed.
Lemma lem4376725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4376726 {_104907 : Type'} (f : type686 _104907) (_50028 : _104907 -> Prop) : (term376 _104907 f _50028) = (term377 _104907 f _50028).
Proof. exact (MK_COMB (@lem4376725) (@lem4376724 _104907 f _50028)). Qed.
Lemma lem4376727 {_104907 : Type'} (_50028 : _104907 -> Prop) (p1 : _104907) : (@I (_104907 -> Prop) _50028 p1) = (@I (_104907 -> Prop) _50028 p1).
Proof. exact (eq_refl (@I (_104907 -> Prop) _50028 p1)). Qed.
Lemma lem4376728 {_104907 : Type'} (f : type686 _104907) (_50028 : _104907 -> Prop) (p1 : _104907) : (term374 _104907 f _50028 p1) = (term378 _104907 f _50028 p1).
Proof. exact (MK_COMB (@lem4376726 _104907 f _50028) (@lem4376727 _104907 _50028 p1)). Qed.
Lemma lem4376729 {_104907 : Type'} (f : type686 _104907) (_50028 : _104907 -> Prop) (p1 : _104907) : (term370 _104907 p1 f _50028) = (term378 _104907 f _50028 p1).
Proof. exact (TRANS (@lem4376721 _104907 f _50028 p1) (@lem4376728 _104907 f _50028 p1)). Qed.
Lemma lem4376732 {_104907 _104908 : Type'} (_50028 : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term378 _104907 f _50028 p1.
Proof. exact (EQ_MP (@lem4376729 _104907 f _50028 p1) (@lem4376718 _104907 _104908 _50028 f g s p1 t p2 h1)). Qed.
Lemma lem4376733 {_104907 _104908 : Type'} (_50028 : _104907 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term378 _104907 f _50028 p1.
Proof. exact (@lem4376732 _104907 _104908 _50028 f g s p1 t p2 h1). Qed.
Lemma lem4376734 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term378 _104907 f s p1.
Proof. exact (@lem4376733 _104907 _104908 s f g s p1 t p2 h1). Qed.
Lemma lem4376737 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I (_104907 -> Prop) s p1.
Proof. exact (@lem4376734 _104907 _104908 f g s p1 t p2 h1 (@lem4376689 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376738 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term379 _104907 s p1.
Proof. exact (fun h0 : term333 _104907 s p1 => @lem4376737 _104907 _104908 f g s p1 t p2 h1). Qed.
Lemma lem4376740 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376741 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term379 _104907 s p1) = (@I (_104907 -> Prop) s p1).
Proof. exact (@lem4376740 (@I (_104907 -> Prop) s p1)). Qed.
Lemma lem4376742 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I (_104907 -> Prop) s p1.
Proof. exact (EQ_MP (@lem4376741 _104907 s p1) (@lem4376738 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376745 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4376747 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term333 _104907 s p1) = (term380 _104907 s p1).
Proof. exact (@lem4376745 (@I (_104907 -> Prop) s p1)). Qed.
Lemma lem4376750 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) (h1 : term333 _104907 s p1) : term380 _104907 s p1.
Proof. exact (EQ_MP (@lem4376747 _104907 s p1) (@lem4376596 _104907 s p1 h1)). Qed.
Lemma lem4376753 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (@lem4376750 _104907 s p1 h1 (@lem4376742 _104907 _104908 f g s p1 t p2 h2)). Qed.
Lemma lem4376754 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : term381.
Proof. exact (fun h0 : ~ False => @lem4376753 _104907 _104908 f g s p1 t p2 h1 h2). Qed.
Lemma lem4376756 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376757 : term381 = False.
Proof. exact (@lem4376756 False). Qed.
Lemma lem4376758 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4376757) (@lem4376754 _104907 _104908 f g s p1 t p2 h1 h2)). Qed.
Lemma lem4376760 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I ((_104908 -> Prop) -> Prop) g t.
Proof. exact (proj2 (@lem4376344 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376761 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term368 _104908 g t.
Proof. exact (fun h0 : term322 _104908 g t => @lem4376760 _104907 _104908 f g s p1 t p2 h1). Qed.
Lemma lem4376763 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376764 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term368 _104908 g t) = (@I ((_104908 -> Prop) -> Prop) g t).
Proof. exact (@lem4376763 (@I ((_104908 -> Prop) -> Prop) g t)). Qed.
Lemma lem4376765 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I ((_104908 -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem4376764 _104908 g t) (@lem4376761 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376771 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4376772 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : (term346 _104908 g _50031 p2) = (term370 _104908 p2 g _50031).
Proof. exact (@lem4376771 (@I (_104908 -> Prop) _50031 p2) (term322 _104908 g _50031)). Qed.
Lemma lem4376778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376779 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : (term371 _104908 g _50031 p2) = (term372 _104908 p2 g _50031).
Proof. exact (MK_COMB (@lem4376778) (@lem4376772 _104908 p2 g _50031)). Qed.
Lemma lem4376785 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : (term370 _104908 p2 g _50031) = (term370 _104908 p2 g _50031).
Proof. exact (eq_refl (term370 _104908 p2 g _50031)). Qed.
Lemma lem4376786 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : ((term346 _104908 g _50031 p2) = (term370 _104908 p2 g _50031)) = ((term370 _104908 p2 g _50031) = (term370 _104908 p2 g _50031)).
Proof. exact (MK_COMB (@lem4376779 _104908 p2 g _50031) (@lem4376785 _104908 p2 g _50031)). Qed.
Lemma lem4376788 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4376789 (x : Prop) : (x = x) = True.
Proof. exact (@lem4376788 Prop x). Qed.
Lemma lem4376790 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : ((term370 _104908 p2 g _50031) = (term370 _104908 p2 g _50031)) = True.
Proof. exact (@lem4376789 (term370 _104908 p2 g _50031)). Qed.
Lemma lem4376791 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : ((term346 _104908 g _50031 p2) = (term370 _104908 p2 g _50031)) = True.
Proof. exact (TRANS (@lem4376786 _104908 p2 g _50031) (@lem4376790 _104908 p2 g _50031)). Qed.
Lemma lem4376792 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : True = ((term346 _104908 g _50031 p2) = (term370 _104908 p2 g _50031)).
Proof. exact (SYM (@lem4376791 _104908 p2 g _50031)). Qed.
Lemma lem4376793 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50031 : _104908 -> Prop) : (term346 _104908 g _50031 p2) = (term370 _104908 p2 g _50031).
Proof. exact (EQ_MP (@lem4376792 _104908 p2 g _50031) (@lem0)). Qed.
Lemma lem4376794 {_104907 _104908 : Type'} (_50031 : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term370 _104908 p2 g _50031.
Proof. exact (EQ_MP (@lem4376793 _104908 p2 g _50031) (@lem4376616 _104907 _104908 _50031 f g s p1 t p2 h1)). Qed.
Lemma lem4376796 (b : Prop) (a : Prop) : (a \/ b) = (term373 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4376797 {_104908 : Type'} (g : type686 _104908) (_50031 : _104908 -> Prop) (p2 : _104908) : (term370 _104908 p2 g _50031) = (term374 _104908 g _50031 p2).
Proof. exact (@lem4376796 (term322 _104908 g _50031) (@I (_104908 -> Prop) _50031 p2)). Qed.
Lemma lem4376799 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4376800 {_104908 : Type'} (g : type686 _104908) (_50031 : _104908 -> Prop) : (term375 _104908 g _50031) = (@I ((_104908 -> Prop) -> Prop) g _50031).
Proof. exact (@lem4376799 (@I ((_104908 -> Prop) -> Prop) g _50031)). Qed.
Lemma lem4376801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4376802 {_104908 : Type'} (g : type686 _104908) (_50031 : _104908 -> Prop) : (term376 _104908 g _50031) = (term377 _104908 g _50031).
Proof. exact (MK_COMB (@lem4376801) (@lem4376800 _104908 g _50031)). Qed.
Lemma lem4376803 {_104908 : Type'} (_50031 : _104908 -> Prop) (p2 : _104908) : (@I (_104908 -> Prop) _50031 p2) = (@I (_104908 -> Prop) _50031 p2).
Proof. exact (eq_refl (@I (_104908 -> Prop) _50031 p2)). Qed.
Lemma lem4376804 {_104908 : Type'} (g : type686 _104908) (_50031 : _104908 -> Prop) (p2 : _104908) : (term374 _104908 g _50031 p2) = (term378 _104908 g _50031 p2).
Proof. exact (MK_COMB (@lem4376802 _104908 g _50031) (@lem4376803 _104908 _50031 p2)). Qed.
Lemma lem4376805 {_104908 : Type'} (g : type686 _104908) (_50031 : _104908 -> Prop) (p2 : _104908) : (term370 _104908 p2 g _50031) = (term378 _104908 g _50031 p2).
Proof. exact (TRANS (@lem4376797 _104908 g _50031 p2) (@lem4376804 _104908 g _50031 p2)). Qed.
Lemma lem4376808 {_104907 _104908 : Type'} (_50031 : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term378 _104908 g _50031 p2.
Proof. exact (EQ_MP (@lem4376805 _104908 g _50031 p2) (@lem4376794 _104907 _104908 _50031 f g s p1 t p2 h1)). Qed.
Lemma lem4376809 {_104907 _104908 : Type'} (_50031 : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term378 _104908 g _50031 p2.
Proof. exact (@lem4376808 _104907 _104908 _50031 f g s p1 t p2 h1). Qed.
Lemma lem4376810 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term378 _104908 g t p2.
Proof. exact (@lem4376809 _104907 _104908 t f g s p1 t p2 h1). Qed.
Lemma lem4376813 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I (_104908 -> Prop) t p2.
Proof. exact (@lem4376810 _104907 _104908 f g s p1 t p2 h1 (@lem4376765 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376814 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : term379 _104908 t p2.
Proof. exact (fun h0 : term333 _104908 t p2 => @lem4376813 _104907 _104908 f g s p1 t p2 h1). Qed.
Lemma lem4376816 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376817 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term379 _104908 t p2) = (@I (_104908 -> Prop) t p2).
Proof. exact (@lem4376816 (@I (_104908 -> Prop) t p2)). Qed.
Lemma lem4376818 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : @I (_104908 -> Prop) t p2.
Proof. exact (EQ_MP (@lem4376817 _104908 t p2) (@lem4376814 _104907 _104908 f g s p1 t p2 h1)). Qed.
Lemma lem4376821 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4376823 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term333 _104908 t p2) = (term380 _104908 t p2).
Proof. exact (@lem4376821 (@I (_104908 -> Prop) t p2)). Qed.
Lemma lem4376826 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) : term380 _104908 t p2.
Proof. exact (EQ_MP (@lem4376823 _104908 t p2) (@lem4376618 _104908 t p2 h1)). Qed.
Lemma lem4376829 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (@lem4376826 _104908 t p2 h1 (@lem4376818 _104907 _104908 f g s p1 t p2 h2)). Qed.
Lemma lem4376830 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : term381.
Proof. exact (fun h0 : ~ False => @lem4376829 _104907 _104908 f g s p1 t p2 h1 h2). Qed.
Lemma lem4376832 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376833 : term381 = False.
Proof. exact (@lem4376832 False). Qed.
Lemma lem4376834 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4376833) (@lem4376830 _104907 _104908 f g s p1 t p2 h1 h2)). Qed.
Lemma lem4376836 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term335 _104907 f s p1) : @I ((_104907 -> Prop) -> Prop) f s.
Proof. exact (proj1 (@lem4376353 _104907 f s p1 h1)). Qed.
Lemma lem4376837 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term335 _104907 f s p1) : term368 _104907 f s.
Proof. exact (fun h0 : term322 _104907 f s => @lem4376836 _104907 f s p1 h1). Qed.
Lemma lem4376839 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376840 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) : (term368 _104907 f s) = (@I ((_104907 -> Prop) -> Prop) f s).
Proof. exact (@lem4376839 (@I ((_104907 -> Prop) -> Prop) f s)). Qed.
Lemma lem4376841 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term335 _104907 f s p1) : @I ((_104907 -> Prop) -> Prop) f s.
Proof. exact (EQ_MP (@lem4376840 _104907 f s) (@lem4376837 _104907 f s p1 h1)). Qed.
Lemma lem4376843 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : @I ((_104908 -> Prop) -> Prop) g x.
Proof. exact (proj1 (@lem4376336 _104907 _104908 g x f x' h1)). Qed.
Lemma lem4376844 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : term368 _104908 g x.
Proof. exact (fun h0 : term322 _104908 g x => @lem4376843 _104907 _104908 g x f x' h1). Qed.
Lemma lem4376846 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376847 {_104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) : (term368 _104908 g x) = (@I ((_104908 -> Prop) -> Prop) g x).
Proof. exact (@lem4376846 (@I ((_104908 -> Prop) -> Prop) g x)). Qed.
Lemma lem4376848 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : @I ((_104908 -> Prop) -> Prop) g x.
Proof. exact (EQ_MP (@lem4376847 _104908 g x) (@lem4376844 _104907 _104908 g x f x' h1)). Qed.
Lemma lem4376864 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4376865 {_104907 _104908 : Type'} (_50032 : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term382 _104907 _104908 g _50033 _50032 p1) = (term383 _104907 _104908 _50032 p1 g _50033).
Proof. exact (@lem4376864 (@I (_104907 -> Prop) _50032 p1) (term322 _104908 g _50033)). Qed.
Lemma lem4376871 {_104907 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) : (term324 _104907 f _50032) = (term324 _104907 f _50032).
Proof. exact (eq_refl (term324 _104907 f _50032)). Qed.
Lemma lem4376872 {_104907 _104908 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) (p1 : _104907) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term366 _104907 _104908 f g _50033 _50032 p1) = (term384 _104907 _104908 f _50032 p1 g _50033).
Proof. exact (MK_COMB (@lem4376871 _104907 f _50032) (@lem4376865 _104907 _104908 _50032 p1 g _50033)). Qed.
Lemma lem4376876 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4376877 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term384 _104907 _104908 f _50032 p1 g _50033) = (term385 _104907 _104908 p1 f _50032 g _50033).
Proof. exact (@lem4376876 (@I (_104907 -> Prop) _50032 p1) (term322 _104907 f _50032) (term322 _104908 g _50033)). Qed.
Lemma lem4376893 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term366 _104907 _104908 f g _50033 _50032 p1) = (term385 _104907 _104908 p1 f _50032 g _50033).
Proof. exact (TRANS (@lem4376872 _104907 _104908 f _50032 p1 g _50033) (@lem4376877 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376895 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term386 _104907 _104908 f g _50033 _50032 p1) = (term387 _104907 _104908 p1 f _50032 g _50033).
Proof. exact (MK_COMB (@lem4376894) (@lem4376893 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376911 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term385 _104907 _104908 p1 f _50032 g _50033) = (term385 _104907 _104908 p1 f _50032 g _50033).
Proof. exact (eq_refl (term385 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376912 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : ((term366 _104907 _104908 f g _50033 _50032 p1) = (term385 _104907 _104908 p1 f _50032 g _50033)) = ((term385 _104907 _104908 p1 f _50032 g _50033) = (term385 _104907 _104908 p1 f _50032 g _50033)).
Proof. exact (MK_COMB (@lem4376895 _104907 _104908 p1 f _50032 g _50033) (@lem4376911 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376914 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4376915 (x : Prop) : (x = x) = True.
Proof. exact (@lem4376914 Prop x). Qed.
Lemma lem4376916 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : ((term385 _104907 _104908 p1 f _50032 g _50033) = (term385 _104907 _104908 p1 f _50032 g _50033)) = True.
Proof. exact (@lem4376915 (term385 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376917 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : ((term366 _104907 _104908 f g _50033 _50032 p1) = (term385 _104907 _104908 p1 f _50032 g _50033)) = True.
Proof. exact (TRANS (@lem4376912 _104907 _104908 p1 f _50032 g _50033) (@lem4376916 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376918 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : True = ((term366 _104907 _104908 f g _50033 _50032 p1) = (term385 _104907 _104908 p1 f _50032 g _50033)).
Proof. exact (SYM (@lem4376917 _104907 _104908 p1 f _50032 g _50033)). Qed.
Lemma lem4376919 {_104907 _104908 : Type'} (p1 : _104907) (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term366 _104907 _104908 f g _50033 _50032 p1) = (term385 _104907 _104908 p1 f _50032 g _50033).
Proof. exact (EQ_MP (@lem4376918 _104907 _104908 p1 f _50032 g _50033) (@lem0)). Qed.
Lemma lem4376920 {_104907 _104908 : Type'} (_50032 : _104907 -> Prop) (_50033 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term385 _104907 _104908 p1 f _50032 g _50033.
Proof. exact (EQ_MP (@lem4376919 _104907 _104908 p1 f _50032 g _50033) (@lem4376638 _104907 _104908 _50033 _50032 s t f g p1 p2 h1)). Qed.
Lemma lem4376922 (b : Prop) (a : Prop) : (a \/ b) = (term373 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4376923 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (p1 : _104907) : (term385 _104907 _104908 p1 f _50032 g _50033) = (term388 _104907 _104908 f g _50033 _50032 p1).
Proof. exact (@lem4376922 (term325 _104907 _104908 f _50032 g _50033) (@I (_104907 -> Prop) _50032 p1)). Qed.
Lemma lem4376925 (a : Prop) (b : Prop) : (term389 a b) = (term390 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4376926 {_104907 _104908 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term391 _104907 _104908 f _50032 g _50033) = (term392 _104907 _104908 f _50032 g _50033).
Proof. exact (@lem4376925 (term322 _104907 f _50032) (term322 _104908 g _50033)). Qed.
Lemma lem4376928 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4376929 {_104907 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) : (term375 _104907 f _50032) = (@I ((_104907 -> Prop) -> Prop) f _50032).
Proof. exact (@lem4376928 (@I ((_104907 -> Prop) -> Prop) f _50032)). Qed.
Lemma lem4376930 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4376931 {_104907 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) : (term393 _104907 f _50032) = (term334 _104907 f _50032).
Proof. exact (MK_COMB (@lem4376930) (@lem4376929 _104907 f _50032)). Qed.
Lemma lem4376933 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4376934 {_104908 : Type'} (g : type686 _104908) (_50033 : _104908 -> Prop) : (term375 _104908 g _50033) = (@I ((_104908 -> Prop) -> Prop) g _50033).
Proof. exact (@lem4376933 (@I ((_104908 -> Prop) -> Prop) g _50033)). Qed.
Lemma lem4376935 {_104907 _104908 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term392 _104907 _104908 f _50032 g _50033) = (term343 _104907 _104908 f _50032 g _50033).
Proof. exact (MK_COMB (@lem4376931 _104907 f _50032) (@lem4376934 _104908 g _50033)). Qed.
Lemma lem4376936 {_104907 _104908 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term391 _104907 _104908 f _50032 g _50033) = (term343 _104907 _104908 f _50032 g _50033).
Proof. exact (TRANS (@lem4376926 _104907 _104908 f _50032 g _50033) (@lem4376935 _104907 _104908 f _50032 g _50033)). Qed.
Lemma lem4376937 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4376938 {_104907 _104908 : Type'} (f : type686 _104907) (_50032 : _104907 -> Prop) (g : type686 _104908) (_50033 : _104908 -> Prop) : (term394 _104907 _104908 f _50032 g _50033) = (term395 _104907 _104908 f _50032 g _50033).
Proof. exact (MK_COMB (@lem4376937) (@lem4376936 _104907 _104908 f _50032 g _50033)). Qed.
Lemma lem4376939 {_104907 : Type'} (_50032 : _104907 -> Prop) (p1 : _104907) : (@I (_104907 -> Prop) _50032 p1) = (@I (_104907 -> Prop) _50032 p1).
Proof. exact (eq_refl (@I (_104907 -> Prop) _50032 p1)). Qed.
Lemma lem4376940 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (p1 : _104907) : (term388 _104907 _104908 f g _50033 _50032 p1) = (term396 _104907 _104908 f g _50033 _50032 p1).
Proof. exact (MK_COMB (@lem4376938 _104907 _104908 f _50032 g _50033) (@lem4376939 _104907 _50032 p1)). Qed.
Lemma lem4376941 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (p1 : _104907) : (term385 _104907 _104908 p1 f _50032 g _50033) = (term396 _104907 _104908 f g _50033 _50032 p1).
Proof. exact (TRANS (@lem4376923 _104907 _104908 f g _50033 _50032 p1) (@lem4376940 _104907 _104908 f g _50033 _50032 p1)). Qed.
Lemma lem4376943 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (x' : _104907 -> Prop) (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) : term343 _104907 _104908 f s g x.
Proof. exact (conj (@lem4376841 _104907 f s p1 h2) (@lem4376848 _104907 _104908 g x f x' h1)). Qed.
Lemma lem4376945 {_104907 _104908 : Type'} (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term396 _104907 _104908 f g _50033 _50032 p1.
Proof. exact (EQ_MP (@lem4376941 _104907 _104908 f g _50033 _50032 p1) (@lem4376920 _104907 _104908 _50032 _50033 s t f g p1 p2 h1)). Qed.
Lemma lem4376946 {_104907 _104908 : Type'} (_50033 : _104908 -> Prop) (_50032 : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term396 _104907 _104908 f g _50033 _50032 p1.
Proof. exact (@lem4376945 _104907 _104908 _50033 _50032 s t f g p1 p2 h1). Qed.
Lemma lem4376947 {_104907 _104908 : Type'} (x : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term396 _104907 _104908 f g x s p1.
Proof. exact (@lem4376946 _104907 _104908 x s s t f g p1 p2 h1). Qed.
Lemma lem4376950 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) (h3 : term339 _104907 _104908 s t f g p1 p2) : @I (_104907 -> Prop) s p1.
Proof. exact (@lem4376947 _104907 _104908 x s t f g p1 p2 h3 (@lem4376943 _104907 _104908 g x x' f s p1 h1 h2)). Qed.
Lemma lem4376951 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) (h3 : term339 _104907 _104908 s t f g p1 p2) : term379 _104907 s p1.
Proof. exact (fun h0 : term333 _104907 s p1 => @lem4376950 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3). Qed.
Lemma lem4376953 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376954 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term379 _104907 s p1) = (@I (_104907 -> Prop) s p1).
Proof. exact (@lem4376953 (@I (_104907 -> Prop) s p1)). Qed.
Lemma lem4376955 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) (h3 : term339 _104907 _104908 s t f g p1 p2) : @I (_104907 -> Prop) s p1.
Proof. exact (EQ_MP (@lem4376954 _104907 s p1) (@lem4376951 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3)). Qed.
Lemma lem4376958 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4376960 {_104907 : Type'} (s : _104907 -> Prop) (p1 : _104907) : (term333 _104907 s p1) = (term380 _104907 s p1).
Proof. exact (@lem4376958 (@I (_104907 -> Prop) s p1)). Qed.
Lemma lem4376963 {_104907 : Type'} (f : type686 _104907) (s : _104907 -> Prop) (p1 : _104907) (h1 : term335 _104907 f s p1) : term380 _104907 s p1.
Proof. exact (EQ_MP (@lem4376960 _104907 s p1) (@lem4376626 _104907 f s p1 h1)). Qed.
Lemma lem4376966 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) (h3 : term339 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (@lem4376963 _104907 f s p1 h2 (@lem4376955 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3)). Qed.
Lemma lem4376967 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) (h3 : term339 _104907 _104908 s t f g p1 p2) : term381.
Proof. exact (fun h0 : ~ False => @lem4376966 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3). Qed.
Lemma lem4376969 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376970 : term381 = False.
Proof. exact (@lem4376969 False). Qed.
Lemma lem4376971 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104907 f s p1) (h3 : term339 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (EQ_MP (@lem4376970) (@lem4376967 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3)). Qed.
Lemma lem4376973 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : @I ((_104907 -> Prop) -> Prop) f x'.
Proof. exact (proj2 (@lem4376336 _104907 _104908 g x f x' h1)). Qed.
Lemma lem4376974 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : term368 _104907 f x'.
Proof. exact (fun h0 : term322 _104907 f x' => @lem4376973 _104907 _104908 g x f x' h1). Qed.
Lemma lem4376976 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376977 {_104907 : Type'} (f : type686 _104907) (x' : _104907 -> Prop) : (term368 _104907 f x') = (@I ((_104907 -> Prop) -> Prop) f x').
Proof. exact (@lem4376976 (@I ((_104907 -> Prop) -> Prop) f x')). Qed.
Lemma lem4376978 {_104907 _104908 : Type'} (g : type686 _104908) (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (h1 : term319 _104907 _104908 g x f x') : @I ((_104907 -> Prop) -> Prop) f x'.
Proof. exact (EQ_MP (@lem4376977 _104907 f x') (@lem4376974 _104907 _104908 g x f x' h1)). Qed.
Lemma lem4376980 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term335 _104908 g t p2) : @I ((_104908 -> Prop) -> Prop) g t.
Proof. exact (proj1 (@lem4376354 _104908 g t p2 h1)). Qed.
Lemma lem4376981 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term335 _104908 g t p2) : term368 _104908 g t.
Proof. exact (fun h0 : term322 _104908 g t => @lem4376980 _104908 g t p2 h1). Qed.
Lemma lem4376983 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4376984 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) : (term368 _104908 g t) = (@I ((_104908 -> Prop) -> Prop) g t).
Proof. exact (@lem4376983 (@I ((_104908 -> Prop) -> Prop) g t)). Qed.
Lemma lem4376985 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term335 _104908 g t p2) : @I ((_104908 -> Prop) -> Prop) g t.
Proof. exact (EQ_MP (@lem4376984 _104908 g t) (@lem4376981 _104908 g t p2 h1)). Qed.
Lemma lem4377001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4377002 {_104908 : Type'} (p2 : _104908) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term346 _104908 g _50035 p2) = (term370 _104908 p2 g _50035).
Proof. exact (@lem4377001 (@I (_104908 -> Prop) _50035 p2) (term322 _104908 g _50035)). Qed.
Lemma lem4377008 {_104907 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) : (term324 _104907 f _50034) = (term324 _104907 f _50034).
Proof. exact (eq_refl (term324 _104907 f _50034)). Qed.
Lemma lem4377009 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (p2 : _104908) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term367 _104907 _104908 f _50034 g _50035 p2) = (term397 _104907 _104908 f _50034 p2 g _50035).
Proof. exact (MK_COMB (@lem4377008 _104907 f _50034) (@lem4377002 _104908 p2 g _50035)). Qed.
Lemma lem4377013 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4377014 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term397 _104907 _104908 f _50034 p2 g _50035) = (term398 _104907 _104908 p2 f _50034 g _50035).
Proof. exact (@lem4377013 (@I (_104908 -> Prop) _50035 p2) (term322 _104907 f _50034) (term322 _104908 g _50035)). Qed.
Lemma lem4377030 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term367 _104907 _104908 f _50034 g _50035 p2) = (term398 _104907 _104908 p2 f _50034 g _50035).
Proof. exact (TRANS (@lem4377009 _104907 _104908 f _50034 p2 g _50035) (@lem4377014 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377031 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4377032 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term399 _104907 _104908 f _50034 g _50035 p2) = (term400 _104907 _104908 p2 f _50034 g _50035).
Proof. exact (MK_COMB (@lem4377031) (@lem4377030 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377048 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term398 _104907 _104908 p2 f _50034 g _50035) = (term398 _104907 _104908 p2 f _50034 g _50035).
Proof. exact (eq_refl (term398 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377049 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : ((term367 _104907 _104908 f _50034 g _50035 p2) = (term398 _104907 _104908 p2 f _50034 g _50035)) = ((term398 _104907 _104908 p2 f _50034 g _50035) = (term398 _104907 _104908 p2 f _50034 g _50035)).
Proof. exact (MK_COMB (@lem4377032 _104907 _104908 p2 f _50034 g _50035) (@lem4377048 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377051 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4377052 (x : Prop) : (x = x) = True.
Proof. exact (@lem4377051 Prop x). Qed.
Lemma lem4377053 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : ((term398 _104907 _104908 p2 f _50034 g _50035) = (term398 _104907 _104908 p2 f _50034 g _50035)) = True.
Proof. exact (@lem4377052 (term398 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377054 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : ((term367 _104907 _104908 f _50034 g _50035 p2) = (term398 _104907 _104908 p2 f _50034 g _50035)) = True.
Proof. exact (TRANS (@lem4377049 _104907 _104908 p2 f _50034 g _50035) (@lem4377053 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377055 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : True = ((term367 _104907 _104908 f _50034 g _50035 p2) = (term398 _104907 _104908 p2 f _50034 g _50035)).
Proof. exact (SYM (@lem4377054 _104907 _104908 p2 f _50034 g _50035)). Qed.
Lemma lem4377056 {_104907 _104908 : Type'} (p2 : _104908) (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term367 _104907 _104908 f _50034 g _50035 p2) = (term398 _104907 _104908 p2 f _50034 g _50035).
Proof. exact (EQ_MP (@lem4377055 _104907 _104908 p2 f _50034 g _50035) (@lem0)). Qed.
Lemma lem4377057 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term398 _104907 _104908 p2 f _50034 g _50035.
Proof. exact (EQ_MP (@lem4377056 _104907 _104908 p2 f _50034 g _50035) (@lem4376682 _104907 _104908 _50034 _50035 s t f g p1 p2 h1)). Qed.
Lemma lem4377059 (b : Prop) (a : Prop) : (a \/ b) = (term373 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4377060 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) (p2 : _104908) : (term398 _104907 _104908 p2 f _50034 g _50035) = (term401 _104907 _104908 f _50034 g _50035 p2).
Proof. exact (@lem4377059 (term325 _104907 _104908 f _50034 g _50035) (@I (_104908 -> Prop) _50035 p2)). Qed.
Lemma lem4377062 (a : Prop) (b : Prop) : (term389 a b) = (term390 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4377063 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term391 _104907 _104908 f _50034 g _50035) = (term392 _104907 _104908 f _50034 g _50035).
Proof. exact (@lem4377062 (term322 _104907 f _50034) (term322 _104908 g _50035)). Qed.
Lemma lem4377065 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4377066 {_104907 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) : (term375 _104907 f _50034) = (@I ((_104907 -> Prop) -> Prop) f _50034).
Proof. exact (@lem4377065 (@I ((_104907 -> Prop) -> Prop) f _50034)). Qed.
Lemma lem4377067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4377068 {_104907 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) : (term393 _104907 f _50034) = (term334 _104907 f _50034).
Proof. exact (MK_COMB (@lem4377067) (@lem4377066 _104907 f _50034)). Qed.
Lemma lem4377070 (a : Prop) : (term81 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4377071 {_104908 : Type'} (g : type686 _104908) (_50035 : _104908 -> Prop) : (term375 _104908 g _50035) = (@I ((_104908 -> Prop) -> Prop) g _50035).
Proof. exact (@lem4377070 (@I ((_104908 -> Prop) -> Prop) g _50035)). Qed.
Lemma lem4377072 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term392 _104907 _104908 f _50034 g _50035) = (term343 _104907 _104908 f _50034 g _50035).
Proof. exact (MK_COMB (@lem4377068 _104907 f _50034) (@lem4377071 _104908 g _50035)). Qed.
Lemma lem4377073 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term391 _104907 _104908 f _50034 g _50035) = (term343 _104907 _104908 f _50034 g _50035).
Proof. exact (TRANS (@lem4377063 _104907 _104908 f _50034 g _50035) (@lem4377072 _104907 _104908 f _50034 g _50035)). Qed.
Lemma lem4377074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4377075 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) : (term394 _104907 _104908 f _50034 g _50035) = (term395 _104907 _104908 f _50034 g _50035).
Proof. exact (MK_COMB (@lem4377074) (@lem4377073 _104907 _104908 f _50034 g _50035)). Qed.
Lemma lem4377076 {_104908 : Type'} (_50035 : _104908 -> Prop) (p2 : _104908) : (@I (_104908 -> Prop) _50035 p2) = (@I (_104908 -> Prop) _50035 p2).
Proof. exact (eq_refl (@I (_104908 -> Prop) _50035 p2)). Qed.
Lemma lem4377077 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) (p2 : _104908) : (term401 _104907 _104908 f _50034 g _50035 p2) = (term402 _104907 _104908 f _50034 g _50035 p2).
Proof. exact (MK_COMB (@lem4377075 _104907 _104908 f _50034 g _50035) (@lem4377076 _104908 _50035 p2)). Qed.
Lemma lem4377078 {_104907 _104908 : Type'} (f : type686 _104907) (_50034 : _104907 -> Prop) (g : type686 _104908) (_50035 : _104908 -> Prop) (p2 : _104908) : (term398 _104907 _104908 p2 f _50034 g _50035) = (term402 _104907 _104908 f _50034 g _50035 p2).
Proof. exact (TRANS (@lem4377060 _104907 _104908 f _50034 g _50035 p2) (@lem4377077 _104907 _104908 f _50034 g _50035 p2)). Qed.
Lemma lem4377080 {_104907 _104908 : Type'} (x : _104908 -> Prop) (f : type686 _104907) (x' : _104907 -> Prop) (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) : term343 _104907 _104908 f x' g t.
Proof. exact (conj (@lem4376978 _104907 _104908 g x f x' h1) (@lem4376985 _104908 g t p2 h2)). Qed.
Lemma lem4377082 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term402 _104907 _104908 f _50034 g _50035 p2.
Proof. exact (EQ_MP (@lem4377078 _104907 _104908 f _50034 g _50035 p2) (@lem4377057 _104907 _104908 _50034 _50035 s t f g p1 p2 h1)). Qed.
Lemma lem4377083 {_104907 _104908 : Type'} (_50034 : _104907 -> Prop) (_50035 : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term402 _104907 _104908 f _50034 g _50035 p2.
Proof. exact (@lem4377082 _104907 _104908 _50034 _50035 s t f g p1 p2 h1). Qed.
Lemma lem4377084 {_104907 _104908 : Type'} (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term339 _104907 _104908 s t f g p1 p2) : term402 _104907 _104908 f x' g t p2.
Proof. exact (@lem4377083 _104907 _104908 x' t s t f g p1 p2 h1). Qed.
Lemma lem4377087 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) (h3 : term339 _104907 _104908 s t f g p1 p2) : @I (_104908 -> Prop) t p2.
Proof. exact (@lem4377084 _104907 _104908 x' s t f g p1 p2 h3 (@lem4377080 _104907 _104908 x f x' g t p2 h1 h2)). Qed.
Lemma lem4377088 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) (h3 : term339 _104907 _104908 s t f g p1 p2) : term379 _104908 t p2.
Proof. exact (fun h0 : term333 _104908 t p2 => @lem4377087 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3). Qed.
Lemma lem4377090 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4377091 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term379 _104908 t p2) = (@I (_104908 -> Prop) t p2).
Proof. exact (@lem4377090 (@I (_104908 -> Prop) t p2)). Qed.
Lemma lem4377092 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) (h3 : term339 _104907 _104908 s t f g p1 p2) : @I (_104908 -> Prop) t p2.
Proof. exact (EQ_MP (@lem4377091 _104908 t p2) (@lem4377088 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3)). Qed.
Lemma lem4377095 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4377097 {_104908 : Type'} (t : _104908 -> Prop) (p2 : _104908) : (term333 _104908 t p2) = (term380 _104908 t p2).
Proof. exact (@lem4377095 (@I (_104908 -> Prop) t p2)). Qed.
Lemma lem4377100 {_104908 : Type'} (g : type686 _104908) (t : _104908 -> Prop) (p2 : _104908) (h1 : term335 _104908 g t p2) : term380 _104908 t p2.
Proof. exact (EQ_MP (@lem4377097 _104908 t p2) (@lem4376658 _104908 g t p2 h1)). Qed.
Lemma lem4377103 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) (h3 : term339 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (@lem4377100 _104908 g t p2 h2 (@lem4377092 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3)). Qed.
Lemma lem4377104 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) (h3 : term339 _104907 _104908 s t f g p1 p2) : term381.
Proof. exact (fun h0 : ~ False => @lem4377103 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3). Qed.
Lemma lem4377106 (p : Prop) : (term369 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4377107 : term381 = False.
Proof. exact (@lem4377106 False). Qed.
Lemma lem4377108 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term335 _104908 g t p2) (h3 : term339 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (EQ_MP (@lem4377107) (@lem4377104 _104907 _104908 x x' s t f g p1 p2 h1 h2 h3)). Qed.
Lemma lem4377109 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : (term333 _104908 t p2) = False.
Proof. exact (prop_ext (fun h3 : term333 _104908 t p2 => @lem4376834 _104907 _104908 f g s p1 t p2 h1 h2) (fun h3 : False => @lem4376618 _104908 t p2 h1)). Qed.
Lemma lem4377110 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4377109 _104907 _104908 f g s p1 t p2 h1 h2) (@lem4376618 _104908 t p2 h1)). Qed.
Lemma lem4377111 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : (term333 _104907 s p1) = False.
Proof. exact (prop_ext (fun h3 : term333 _104907 s p1 => @lem4376758 _104907 _104908 f g s p1 t p2 h1 h2) (fun h3 : False => @lem4376596 _104907 s p1 h1)). Qed.
Lemma lem4377112 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4377111 _104907 _104908 f g s p1 t p2 h1 h2) (@lem4376596 _104907 s p1 h1)). Qed.
Lemma lem4377113 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : (term333 _104908 t p2) = False.
Proof. exact (prop_ext (fun h3 : term333 _104908 t p2 => @lem4377110 _104907 _104908 f g s p1 t p2 h1 h2) (fun h3 : False => @lem4376450 _104908 t p2 h1)). Qed.
Lemma lem4377114 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4377113 _104907 _104908 f g s p1 t p2 h1 h2) (@lem4376450 _104908 t p2 h1)). Qed.
Lemma lem4377115 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : (term333 _104907 s p1) = False.
Proof. exact (prop_ext (fun h3 : term333 _104907 s p1 => @lem4377112 _104907 _104908 f g s p1 t p2 h1 h2) (fun h3 : False => @lem4376404 _104907 s p1 h1)). Qed.
Lemma lem4377116 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4377115 _104907 _104908 f g s p1 t p2 h1 h2) (@lem4376404 _104907 s p1 h1)). Qed.
Lemma lem4377117 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : (term333 _104908 t p2) = False.
Proof. exact (prop_ext (fun h3 : term333 _104908 t p2 => @lem4377114 _104907 _104908 f g s p1 t p2 h1 h2) (fun h3 : False => @lem4376450 _104908 t p2 h1)). Qed.
Lemma lem4377118 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104908 t p2) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4377117 _104907 _104908 f g s p1 t p2 h1 h2) (@lem4376450 _104908 t p2 h1)). Qed.
Lemma lem4377119 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : (term333 _104907 s p1) = False.
Proof. exact (prop_ext (fun h3 : term333 _104907 s p1 => @lem4377116 _104907 _104908 f g s p1 t p2 h1 h2) (fun h3 : False => @lem4376404 _104907 s p1 h1)). Qed.
Lemma lem4377120 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term333 _104907 s p1) (h2 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (EQ_MP (@lem4377119 _104907 _104908 f g s p1 t p2 h1 h2) (@lem4376404 _104907 s p1 h1)). Qed.
Lemma lem4377121 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term339 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (or_elim (@lem4376352 _104907 _104908 s t f g p1 p2 h2) (fun h0 : term335 _104907 f s p1 => @lem4376971 _104907 _104908 x x' s t f g p1 p2 h1 h0 h2) (fun h0 : term335 _104908 g t p2 => @lem4377108 _104907 _104908 x x' s t f g p1 p2 h1 h0 h2)). Qed.
Lemma lem4377122 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (s : _104907 -> Prop) (p1 : _104907) (t : _104908 -> Prop) (p2 : _104908) (h1 : term352 _104907 _104908 f g s p1 t p2) : False.
Proof. exact (or_elim (@lem4376343 _104907 _104908 f g s p1 t p2 h1) (fun h0 : term333 _104907 s p1 => @lem4377120 _104907 _104908 f g s p1 t p2 h0 h1) (fun h0 : term333 _104908 t p2 => @lem4377118 _104907 _104908 f g s p1 t p2 h0 h1)). Qed.
Lemma lem4377123 {_104907 _104908 : Type'} (x : _104908 -> Prop) (x' : _104907 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term319 _104907 _104908 g x f x') (h2 : term313 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (or_elim (@lem4376316 _104907 _104908 s t f g p1 p2 h2) (fun h0 : term352 _104907 _104908 f g s p1 t p2 => @lem4377122 _104907 _104908 f g s p1 t p2 h0) (fun h0 : term339 _104907 _104908 s t f g p1 p2 => @lem4377121 _104907 _104908 x x' s t f g p1 p2 h1 h0)). Qed.
Lemma lem4377124 {_104907 _104908 : Type'} (x : _104908 -> Prop) (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term113 _104907 _104908 g x f) (h2 : term313 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (ex_elim (@lem4376113 _104907 _104908 g x f h1) (fun x' : _104907 -> Prop => fun h0 : term403 _104907 _104908 g x f x' => @lem4377123 _104907 _104908 x x' s t f g p1 p2 h0 h2)). Qed.
Lemma lem4377125 {_104907 _104908 : Type'} (s : _104907 -> Prop) (t : _104908 -> Prop) (f : type686 _104907) (g : type686 _104908) (p1 : _104907) (p2 : _104908) (h1 : term29 _104907 _104908 g f) (h2 : term313 _104907 _104908 s t f g p1 p2) : False.
Proof. exact (ex_elim (@lem4375490 _104907 _104908 g f h1) (fun x : _104908 -> Prop => fun h0 : term115 _104907 _104908 g f x => @lem4377124 _104907 _104908 x s t f g p1 p2 h0 h2)). Qed.
Lemma lem4377126 {_104907 _104908 : Type'} (s : _104907 -> Prop) (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : term316 _104907 _104908 s f g p1 p2) (h2 : term29 _104907 _104908 g f) : False.
Proof. exact (ex_elim (@lem4376111 _104907 _104908 s f g p1 p2 h1) (fun t : _104908 -> Prop => fun h0 : term315 _104907 _104908 s f g p1 p2 t => @lem4377125 _104907 _104908 s t f g p1 p2 h2 h0)). Qed.
Lemma lem4377127 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : term91 _104907 _104908 f g p1 p2) (h2 : term29 _104907 _104908 g f) : False.
Proof. exact (ex_elim (@lem4376110 _104907 _104908 f g p1 p2 h1) (fun s : _104907 -> Prop => fun h0 : term317 _104907 _104908 f g p1 p2 s => @lem4377126 _104907 _104908 s p1 p2 g f h0 h2)). Qed.
Lemma lem4377128 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : term91 _104907 _104908 f g p1 p2) (h2 : term29 _104907 _104908 g f) : (term91 _104907 _104908 f g p1 p2) = False.
Proof. exact (prop_ext (fun h3 : term91 _104907 _104908 f g p1 p2 => @lem4377127 _104907 _104908 p1 p2 g f h1 h2) (fun h3 : False => @lem4375437 _104907 _104908 f g p1 p2 h1)). Qed.
Lemma lem4377129 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : term91 _104907 _104908 f g p1 p2) (h2 : term29 _104907 _104908 g f) : False.
Proof. exact (EQ_MP (@lem4377128 _104907 _104908 p1 p2 g f h1 h2) (@lem4375437 _104907 _104908 f g p1 p2 h1)). Qed.
Lemma lem4377130 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : term29 _104907 _104908 g f) : term90 _104907 _104908 f g p1 p2.
Proof. exact (fun h0 : term91 _104907 _104908 f g p1 p2 => @lem4377129 _104907 _104908 p1 p2 g f h0 h1). Qed.
Lemma lem4377131 {_104907 _104908 : Type'} (p1 : _104907) (p2 : _104908) (g : type686 _104908) (f : type686 _104907) (h1 : term29 _104907 _104908 g f) : (term43 _104907 _104908 f p1 g p2) = (term65 _104907 _104908 f g p1 p2).
Proof. exact (EQ_MP (@lem4375436 _104907 _104908 f g p1 p2) (@lem4377130 _104907 _104908 p1 p2 g f h1)). Qed.
Lemma lem4377136 {_104907 _104908 : Type'} (p1 : _104907) (g : type686 _104908) (f : type686 _104907) (h1 : term29 _104907 _104908 g f) : term69 _104907 _104908 f g p1.
Proof. exact (fun p2 : _104908 => @lem4377131 _104907 _104908 p1 p2 g f h1). Qed.
Lemma lem4377141 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) (h1 : term29 _104907 _104908 g f) : term72 _104907 _104908 f g.
Proof. exact (fun p1 : _104907 => @lem4377136 _104907 _104908 p1 g f h1). Qed.
Lemma lem4377142 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term73 _104907 _104908 f g.
Proof. exact (fun h0 : term29 _104907 _104908 g f => @lem4377141 _104907 _104908 g f h0). Qed.
Lemma lem4377147 {_104907 _104908 : Type'} (g : type686 _104908) : term85 _104907 _104908 g.
Proof. exact (fun f : type686 _104907 => @lem4377142 _104907 _104908 f g). Qed.
Lemma lem4377152 {_104907 _104908 : Type'} : term89 _104907 _104908.
Proof. exact (fun g : type686 _104908 => @lem4377147 _104907 _104908 g). Qed.
Lemma lem4377153 {_104907 _104908 : Type'} : term88 _104907 _104908.
Proof. exact (EQ_MP (@lem4375431 _104907 _104908) (@lem4377152 _104907 _104908)). Qed.
Lemma lem4377154 {_104907 _104908 : Type'} (g : type686 _104908) : term404 _104907 _104908 g.
Proof. exact (@lem4377153 _104907 _104908 g). Qed.
Lemma lem4377155 {_104907 _104908 : Type'} (g : type686 _104908) : (term404 _104907 _104908 g) = (term84 _104907 _104908 g).
Proof. exact (eq_refl (term404 _104907 _104908 g)). Qed.
Lemma lem4377156 {_104907 _104908 : Type'} (g : type686 _104908) : term84 _104907 _104908 g.
Proof. exact (EQ_MP (@lem4377155 _104907 _104908 g) (@lem4377154 _104907 _104908 g)). Qed.
Lemma lem4377157 {_104907 _104908 : Type'} (g : type686 _104908) (f : type686 _104907) : term405 _104907 _104908 g f.
Proof. exact (@lem4377156 _104907 _104908 g f). Qed.
Lemma lem4377158 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : (term405 _104907 _104908 g f) = (term75 _104907 _104908 f g).
Proof. exact (eq_refl (term405 _104907 _104908 g f)). Qed.
Lemma lem4377159 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term75 _104907 _104908 f g.
Proof. exact (EQ_MP (@lem4377158 _104907 _104908 f g) (@lem4377157 _104907 _104908 g f)). Qed.
Lemma lem4377161 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term75 _104907 _104908 f g.
Proof. exact (@lem4375195 _104907 _104908 f g (@lem4377159 _104907 _104908 f g)). Qed.
Lemma lem4377162 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term76 _104907 _104908 f g) : False.
Proof. exact (@lem4377161 _104907 _104908 f g (@lem4375179 _104907 _104908 f g h1)). Qed.
Lemma lem4377163 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term76 _104907 _104908 f g) : (term76 _104907 _104908 f g) = False.
Proof. exact (prop_ext (fun h2 : term76 _104907 _104908 f g => @lem4377162 _104907 _104908 f g h1) (fun h2 : False => @lem4375179 _104907 _104908 f g h1)). Qed.
Lemma lem4377164 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term76 _104907 _104908 f g) : False.
Proof. exact (EQ_MP (@lem4377163 _104907 _104908 f g h1) (@lem4375179 _104907 _104908 f g h1)). Qed.
Lemma lem4377165 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term75 _104907 _104908 f g.
Proof. exact (fun h0 : term76 _104907 _104908 f g => @lem4377164 _104907 _104908 f g h0). Qed.
Lemma lem4377166 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term73 _104907 _104908 f g.
Proof. exact (EQ_MP (@lem4375178 _104907 _104908 f g) (@lem4377165 _104907 _104908 f g)). Qed.
Lemma lem4377167 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term20 _104907 _104908 f g.
Proof. exact (EQ_MP (@lem4375174 _104907 _104908 f g) (@lem4377166 _104907 _104908 f g)). Qed.
Lemma lem4377168 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) : term19 _104907 _104908 f g.
Proof. exact (EQ_MP (@lem4374944 _104907 _104908 f g) (@lem4377167 _104907 _104908 f g)). Qed.
Lemma lem4377169 {_104907 _104908 : Type'} (f : type686 _104907) (g : type686 _104908) (h1 : term7 _104907 f) (h2 : term7 _104908 g) : term18 _104907 _104908 f g.
Proof. exact (@lem4377168 _104907 _104908 f g (@lem4374868 _104907 _104908 f g h1 h2)). Qed.
