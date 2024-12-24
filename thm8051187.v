Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm8051187_term_abbrevs.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211668_spec.
Require Import thm3211669_spec.
Require Import thm3211724_spec.
Require Import thm3211725_spec.
Require Import thm3211729_spec.
Require Import thm3211730_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm8048850_spec.
Lemma lem8050956 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem8050957 {_142951 _142952 : Type'} (s : type56 _142951 _142952) (t : type56 _142951 _142952) : (s = t) = (term1 _142951 _142952 s t).
Proof. exact (@lem8050956 (type24 _142951 _142952) s t). Qed.
Lemma lem8050958 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (f = (@EMPTY ((cart _142951 _142952) -> Prop))) = (term2 _142951 _142952 f).
Proof. exact (@lem8050957 _142951 _142952 f (@EMPTY ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8050967 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8050968 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term3 _142951 _142952 f) = (term4 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8050967) (@lem8050958 _142951 _142952 f)). Qed.
Lemma lem8050991 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term5 _142951 _142952 _142953 g) = (term5 _142951 _142952 _142953 g).
Proof. exact (eq_refl (term5 _142951 _142952 _142953 g)). Qed.
Lemma lem8050992 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term6 _142951 _142952 _142953 f g) = (term7 _142951 _142952 _142953 f g).
Proof. exact (MK_COMB (@lem8050968 _142951 _142952 f) (@lem8050991 _142951 _142952 _142953 g)). Qed.
Lemma lem8050995 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term7 _142951 _142952 _142953 f g) = (term6 _142951 _142952 _142953 f g).
Proof. exact (SYM (@lem8050992 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051005 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051006 {_142951 _142952 : Type'} (P : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x P) = (P x).
Proof. exact (@lem8051005 (type24 _142951 _142952) P x). Qed.
Lemma lem8051007 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x f) = (f x).
Proof. exact (@lem8051006 _142951 _142952 f x). Qed.
Lemma lem8051008 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051009 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : (term8 _142951 _142952 x f) = (term9 _142951 _142952 f x).
Proof. exact (MK_COMB (@lem8051008) (@lem8051007 _142951 _142952 f x)). Qed.
Lemma lem8051011 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051012 {_142951 _142952 : Type'} (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop))) = False.
Proof. exact (@lem8051011 (type24 _142951 _142952) x). Qed.
Lemma lem8051013 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((@IN ((cart _142951 _142952) -> Prop) x f) = (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop)))) = ((f x) = False).
Proof. exact (MK_COMB (@lem8051009 _142951 _142952 f x) (@lem8051012 _142951 _142952 x)). Qed.
Lemma lem8051015 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem1857 t)). Qed.
Lemma lem8051016 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((f x) = False) = (term10 _142951 _142952 f x).
Proof. exact (@lem8051015 (f x)). Qed.
Lemma lem8051017 {_142951 _142952 : Type'} (f : type56 _142951 _142952) (x : type24 _142951 _142952) : ((@IN ((cart _142951 _142952) -> Prop) x f) = (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop)))) = (term10 _142951 _142952 f x).
Proof. exact (TRANS (@lem8051013 _142951 _142952 f x) (@lem8051016 _142951 _142952 f x)). Qed.
Lemma lem8051018 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term11 _142951 _142952 f) = (term12 _142951 _142952 f).
Proof. exact (fun_ext (fun x : type24 _142951 _142952 => @lem8051017 _142951 _142952 f x)). Qed.
Lemma lem8051019 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051020 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term2 _142951 _142952 f) = (term13 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051019 _142951 _142952) (@lem8051018 _142951 _142952 f)). Qed.
Lemma lem8051025 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051026 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term4 _142951 _142952 f) = (term14 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051025) (@lem8051020 _142951 _142952 f)). Qed.
Lemma lem8051040 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8051041 {_142951 _142952 : Type'} (s : type56 _142951 _142952) (x : cart _142951 _142952) : (term17 _142951 _142952 x s) = (term18 _142951 _142952 s x).
Proof. exact (@lem8051040 (cart _142951 _142952) s x). Qed.
Lemma lem8051042 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term19 _142951 _142952 x) = (term20 _142951 _142952 x).
Proof. exact (@lem8051041 _142951 _142952 (@EMPTY ((cart _142951 _142952) -> Prop)) x). Qed.
Lemma lem8051050 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem3211730 A x (@lem3211729 A x)). Qed.
Lemma lem8051051 {_142951 _142952 : Type'} (x : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) x (@EMPTY ((cart _142951 _142952) -> Prop))) = False.
Proof. exact (@lem8051050 (type24 _142951 _142952) x). Qed.
Lemma lem8051052 {_142951 _142952 : Type'} (t : type24 _142951 _142952) : (@IN ((cart _142951 _142952) -> Prop) t (@EMPTY ((cart _142951 _142952) -> Prop))) = False.
Proof. exact (@lem8051051 _142951 _142952 t). Qed.
Lemma lem8051053 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051054 {_142951 _142952 : Type'} (t : type24 _142951 _142952) : (term21 _142951 _142952 t) = (imp False).
Proof. exact (MK_COMB (@lem8051053) (@lem8051052 _142951 _142952 t)). Qed.
Lemma lem8051056 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051057 {_142951 _142952 : Type'} (P : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x P) = (P x).
Proof. exact (@lem8051056 (cart _142951 _142952) P x). Qed.
Lemma lem8051058 {_142951 _142952 : Type'} (t : type24 _142951 _142952) (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x t) = (t x).
Proof. exact (@lem8051057 _142951 _142952 t x). Qed.
Lemma lem8051059 {_142951 _142952 : Type'} (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term22 _142951 _142952 x t) = (term23 _142951 _142952 t x).
Proof. exact (MK_COMB (@lem8051054 _142951 _142952 t) (@lem8051058 _142951 _142952 t x)). Qed.
Lemma lem8051061 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem8051062 {_142951 _142952 : Type'} (t : type24 _142951 _142952) (x : cart _142951 _142952) : (term23 _142951 _142952 t x) = True.
Proof. exact (@lem8051061 (t x)). Qed.
Lemma lem8051063 {_142951 _142952 : Type'} (x : cart _142951 _142952) (t : type24 _142951 _142952) : (term22 _142951 _142952 x t) = True.
Proof. exact (TRANS (@lem8051059 _142951 _142952 t x) (@lem8051062 _142951 _142952 t x)). Qed.
Lemma lem8051064 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term24 _142951 _142952 x) = (term25 _142951 _142952).
Proof. exact (fun_ext (fun t : type24 _142951 _142952 => @lem8051063 _142951 _142952 x t)). Qed.
Lemma lem8051065 {_142951 _142952 : Type'} : (@all ((cart _142951 _142952) -> Prop)) = (@all ((cart _142951 _142952) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142952) -> Prop))). Qed.
Lemma lem8051066 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term20 _142951 _142952 x) = (term26 _142951 _142952).
Proof. exact (MK_COMB (@lem8051065 _142951 _142952) (@lem8051064 _142951 _142952 x)). Qed.
Lemma lem8051068 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8051069 {_142951 _142952 : Type'} (t : Prop) : (term28 _142951 _142952 t) = t.
Proof. exact (@lem8051068 (type24 _142951 _142952) t). Qed.
Lemma lem8051070 {_142951 _142952 : Type'} : (term26 _142951 _142952) = True.
Proof. exact (@lem8051069 _142951 _142952 True). Qed.
Lemma lem8051071 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term20 _142951 _142952 x) = True.
Proof. exact (TRANS (@lem8051066 _142951 _142952 x) (@lem8051070 _142951 _142952)). Qed.
Lemma lem8051072 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term19 _142951 _142952 x) = True.
Proof. exact (TRANS (@lem8051042 _142951 _142952 x) (@lem8051071 _142951 _142952 x)). Qed.
Lemma lem8051073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051074 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term29 _142951 _142952 x) = (and True).
Proof. exact (MK_COMB (@lem8051073) (@lem8051072 _142951 _142952 x)). Qed.
Lemma lem8051076 {A : Type'} (s : type686 A) (x : A) : (term15 A x s) = (term16 A s x).
Proof. exact (EQ_MP (@lem3211669 A s x) (@lem3211668 A s x)). Qed.
Lemma lem8051077 {_142951 _142953 : Type'} (s : type56 _142951 _142953) (x : cart _142951 _142953) : (term17 _142951 _142953 x s) = (term18 _142951 _142953 s x).
Proof. exact (@lem8051076 (cart _142951 _142953) s x). Qed.
Lemma lem8051078 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term17 _142951 _142953 y g) = (term18 _142951 _142953 g y).
Proof. exact (@lem8051077 _142951 _142953 g y). Qed.
Lemma lem8051086 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051087 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x P) = (P x).
Proof. exact (@lem8051086 (type24 _142951 _142953) P x). Qed.
Lemma lem8051088 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) t g) = (g t).
Proof. exact (@lem8051087 _142951 _142953 g t). Qed.
Lemma lem8051089 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051090 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term30 _142951 _142953 t g) = (term31 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8051089) (@lem8051088 _142951 _142953 g t)). Qed.
Lemma lem8051092 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051093 {_142951 _142953 : Type'} (P : type24 _142951 _142953) (x : cart _142951 _142953) : (@IN (cart _142951 _142953) x P) = (P x).
Proof. exact (@lem8051092 (cart _142951 _142953) P x). Qed.
Lemma lem8051094 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y t) = (t y).
Proof. exact (@lem8051093 _142951 _142953 t y). Qed.
Lemma lem8051095 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term32 _142951 _142953 g y t) = (term33 _142951 _142953 g t y).
Proof. exact (MK_COMB (@lem8051090 _142951 _142953 g t) (@lem8051094 _142951 _142953 t y)). Qed.
Lemma lem8051098 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term34 _142951 _142953 g y) = (term35 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051095 _142951 _142953 g t y)). Qed.
Lemma lem8051099 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051100 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term18 _142951 _142953 g y) = (term36 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8051099 _142951 _142953) (@lem8051098 _142951 _142953 g y)). Qed.
Lemma lem8051105 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term17 _142951 _142953 y g) = (term36 _142951 _142953 g y).
Proof. exact (TRANS (@lem8051078 _142951 _142953 g y) (@lem8051100 _142951 _142953 g y)). Qed.
Lemma lem8051106 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term37 _142951 _142952 _142953 x y g) = (term38 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8051074 _142951 _142952 x) (@lem8051105 _142951 _142953 g y)). Qed.
Lemma lem8051108 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8051109 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term38 _142951 _142953 g y) = (term36 _142951 _142953 g y).
Proof. exact (@lem8051108 (term36 _142951 _142953 g y)). Qed.
Lemma lem8051116 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term37 _142951 _142952 _142953 x y g) = (term36 _142951 _142953 g y).
Proof. exact (TRANS (@lem8051106 _142951 _142952 _142953 x g y) (@lem8051109 _142951 _142953 g y)). Qed.
Lemma lem8051117 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem8051118 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term39 _142951 _142952 _142953 x y g) = (term40 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8051117) (@lem8051116 _142951 _142952 _142953 x g y)). Qed.
Lemma lem8051126 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051127 {_142951 _142953 : Type'} (P : type56 _142951 _142953) (x : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) x P) = (P x).
Proof. exact (@lem8051126 (type24 _142951 _142953) P x). Qed.
Lemma lem8051128 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (@IN ((cart _142951 _142953) -> Prop) t g) = (g t).
Proof. exact (@lem8051127 _142951 _142953 g t). Qed.
Lemma lem8051129 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem8051130 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (t : type24 _142951 _142953) : (term30 _142951 _142953 t g) = (term31 _142951 _142953 g t).
Proof. exact (MK_COMB (@lem8051129) (@lem8051128 _142951 _142953 g t)). Qed.
Lemma lem8051134 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem3211725 A x) (@lem3211724 A x)). Qed.
Lemma lem8051135 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (@IN (cart _142951 _142952) x (@UNIV (cart _142951 _142952))) = True.
Proof. exact (@lem8051134 (cart _142951 _142952) x). Qed.
Lemma lem8051136 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem8051137 {_142951 _142952 : Type'} (x : cart _142951 _142952) : (term41 _142951 _142952 x) = (and True).
Proof. exact (MK_COMB (@lem8051136) (@lem8051135 _142951 _142952 x)). Qed.
Lemma lem8051139 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem8051140 {_142951 _142953 : Type'} (P : type24 _142951 _142953) (x : cart _142951 _142953) : (@IN (cart _142951 _142953) x P) = (P x).
Proof. exact (@lem8051139 (cart _142951 _142953) P x). Qed.
Lemma lem8051141 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (@IN (cart _142951 _142953) y t) = (t y).
Proof. exact (@lem8051140 _142951 _142953 t y). Qed.
Lemma lem8051142 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term42 _142951 _142952 _142953 x y t) = (term43 _142951 _142953 t y).
Proof. exact (MK_COMB (@lem8051137 _142951 _142952 x) (@lem8051141 _142951 _142953 t y)). Qed.
Lemma lem8051144 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem8051145 {_142951 _142953 : Type'} (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term43 _142951 _142953 t y) = (t y).
Proof. exact (@lem8051144 (t y)). Qed.
Lemma lem8051146 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term42 _142951 _142952 _142953 x y t) = (t y).
Proof. exact (TRANS (@lem8051142 _142951 _142952 _142953 x t y) (@lem8051145 _142951 _142953 t y)). Qed.
Lemma lem8051147 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (t : type24 _142951 _142953) (y : cart _142951 _142953) : (term44 _142951 _142952 _142953 g x y t) = (term33 _142951 _142953 g t y).
Proof. exact (MK_COMB (@lem8051130 _142951 _142953 g t) (@lem8051146 _142951 _142952 _142953 x t y)). Qed.
Lemma lem8051150 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term45 _142951 _142952 _142953 g x y) = (term35 _142951 _142953 g y).
Proof. exact (fun_ext (fun t : type24 _142951 _142953 => @lem8051147 _142951 _142952 _142953 x g t y)). Qed.
Lemma lem8051151 {_142951 _142953 : Type'} : (@all ((cart _142951 _142953) -> Prop)) = (@all ((cart _142951 _142953) -> Prop)).
Proof. exact (eq_refl (@all ((cart _142951 _142953) -> Prop))). Qed.
Lemma lem8051152 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : (term46 _142951 _142952 _142953 g x y) = (term36 _142951 _142953 g y).
Proof. exact (MK_COMB (@lem8051151 _142951 _142953) (@lem8051150 _142951 _142952 _142953 x g y)). Qed.
Lemma lem8051157 {_142951 _142952 _142953 : Type'} (x : cart _142951 _142952) (g : type56 _142951 _142953) (y : cart _142951 _142953) : ((term37 _142951 _142952 _142953 x y g) = (term46 _142951 _142952 _142953 g x y)) = ((term36 _142951 _142953 g y) = (term36 _142951 _142953 g y)).
Proof. exact (MK_COMB (@lem8051118 _142951 _142952 _142953 x g y) (@lem8051152 _142951 _142952 _142953 x g y)). Qed.
Lemma lem8051159 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem8051160 (x : Prop) : (x = x) = True.
Proof. exact (@lem8051159 Prop x). Qed.
Lemma lem8051161 {_142951 _142953 : Type'} (g : type56 _142951 _142953) (y : cart _142951 _142953) : ((term36 _142951 _142953 g y) = (term36 _142951 _142953 g y)) = True.
Proof. exact (@lem8051160 (term36 _142951 _142953 g y)). Qed.
Lemma lem8051162 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) (y : cart _142951 _142953) : ((term37 _142951 _142952 _142953 x y g) = (term46 _142951 _142952 _142953 g x y)) = True.
Proof. exact (TRANS (@lem8051157 _142951 _142952 _142953 x g y) (@lem8051161 _142951 _142953 g y)). Qed.
Lemma lem8051163 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term47 _142951 _142952 _142953 g x) = (term48 _142951 _142953).
Proof. exact (fun_ext (fun y : cart _142951 _142953 => @lem8051162 _142951 _142952 _142953 g x y)). Qed.
Lemma lem8051164 {_142951 _142953 : Type'} : (@all (cart _142951 _142953)) = (@all (cart _142951 _142953)).
Proof. exact (eq_refl (@all (cart _142951 _142953))). Qed.
Lemma lem8051165 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term49 _142951 _142952 _142953 g x) = (term50 _142951 _142953).
Proof. exact (MK_COMB (@lem8051164 _142951 _142953) (@lem8051163 _142951 _142952 _142953 g x)). Qed.
Lemma lem8051167 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8051168 {_142951 _142953 : Type'} (t : Prop) : (term51 _142951 _142953 t) = t.
Proof. exact (@lem8051167 (cart _142951 _142953) t). Qed.
Lemma lem8051169 {_142951 _142953 : Type'} : (term50 _142951 _142953) = True.
Proof. exact (@lem8051168 _142951 _142953 True). Qed.
Lemma lem8051170 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (x : cart _142951 _142952) : (term49 _142951 _142952 _142953 g x) = True.
Proof. exact (TRANS (@lem8051165 _142951 _142952 _142953 g x) (@lem8051169 _142951 _142953)). Qed.
Lemma lem8051171 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term52 _142951 _142952 _142953 g) = (term48 _142951 _142952).
Proof. exact (fun_ext (fun x : cart _142951 _142952 => @lem8051170 _142951 _142952 _142953 g x)). Qed.
Lemma lem8051172 {_142951 _142952 : Type'} : (@all (cart _142951 _142952)) = (@all (cart _142951 _142952)).
Proof. exact (eq_refl (@all (cart _142951 _142952))). Qed.
Lemma lem8051173 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term5 _142951 _142952 _142953 g) = (term50 _142951 _142952).
Proof. exact (MK_COMB (@lem8051172 _142951 _142952) (@lem8051171 _142951 _142952 _142953 g)). Qed.
Lemma lem8051175 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem8051176 {_142951 _142952 : Type'} (t : Prop) : (term51 _142951 _142952 t) = t.
Proof. exact (@lem8051175 (cart _142951 _142952) t). Qed.
Lemma lem8051177 {_142951 _142952 : Type'} : (term50 _142951 _142952) = True.
Proof. exact (@lem8051176 _142951 _142952 True). Qed.
Lemma lem8051178 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) : (term5 _142951 _142952 _142953 g) = True.
Proof. exact (TRANS (@lem8051173 _142951 _142952 _142953 g) (@lem8051177 _142951 _142952)). Qed.
Lemma lem8051179 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) : (term7 _142951 _142952 _142953 f g) = (term53 _142951 _142952 f).
Proof. exact (MK_COMB (@lem8051026 _142951 _142952 f) (@lem8051178 _142951 _142952 _142953 g)). Qed.
Lemma lem8051181 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem8051182 {_142951 _142952 : Type'} (f : type56 _142951 _142952) : (term53 _142951 _142952 f) = True.
Proof. exact (@lem8051181 (term13 _142951 _142952 f)). Qed.
Lemma lem8051183 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : (term7 _142951 _142952 _142953 f g) = True.
Proof. exact (TRANS (@lem8051179 _142951 _142952 _142953 g f) (@lem8051182 _142951 _142952 f)). Qed.
Lemma lem8051184 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : True = (term7 _142951 _142952 _142953 f g).
Proof. exact (SYM (@lem8051183 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051185 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term7 _142951 _142952 _142953 f g.
Proof. exact (EQ_MP (@lem8051184 _142951 _142952 _142953 f g) (@lem0)). Qed.
Lemma lem8051186 {_142951 _142952 _142953 : Type'} (f : type56 _142951 _142952) (g : type56 _142951 _142953) : term6 _142951 _142952 _142953 f g.
Proof. exact (EQ_MP (@lem8050995 _142951 _142952 _142953 f g) (@lem8051185 _142951 _142952 _142953 f g)). Qed.
Lemma lem8051187 {_142951 _142952 _142953 : Type'} (g : type56 _142951 _142953) (f : type56 _142951 _142952) (h1 : f = (@EMPTY ((cart _142951 _142952) -> Prop))) : term5 _142951 _142952 _142953 g.
Proof. exact (@lem8051186 _142951 _142952 _142953 f g (@lem8048850 _142951 _142952 f h1)). Qed.
